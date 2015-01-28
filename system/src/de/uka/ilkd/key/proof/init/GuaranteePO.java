package de.uka.ilkd.key.proof.init;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Properties;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.DisplayableSpecificationElement;
import de.uka.ilkd.key.speclang.ThreadSpecification;

/**
 * Proof obligation for rely/guarantee.
 * It includes the trace property for guarantee (including framing)
 * and reflexivity/transitivity for the rely condition.
 * @author bruns
 * @since 2.3.7349
 */
public class GuaranteePO extends AbstractPO {

    private final static String THREAD = "java.lang.Thread";
    private final static String NAME = ".Thread Specification";
    private final static String RUN = "run";
    
    private final TermBuilder tb;
    protected final ThreadSpecification tspec;
    
    public GuaranteePO (InitConfig initConfig, ThreadSpecification tspec) {
        super(initConfig, tspec.getKJT()+NAME);
        final KeYJavaType threadType = javaInfo.getTypeByClassName(THREAD);
        if (! javaInfo.isSubtype(tspec.getKJT(), threadType))
            throw new IllegalArgumentException("Thread specification must be associated " +
                                               "to a subtype of java.lang.Thread");
        this.tspec = tspec;
        tb = environmentServices.getTermBuilder();
    }

    @Override
    protected InitConfig getCreatedInitConfigForSingleProof() {
        return environmentConfig;
    }

    /**
     * Builds the "general assumption".
     * @param thread The thread variable.
     * @param threadType The type of the according thread.
     * @param target The target.
     * @return The {@link Term} containing the general assumptions.
     */
    private Term buildFreePre(final Term thread,
                              final KeYJavaType threadType,
                              final LocationVariable target) {
        final TypeConverter tc = environmentServices.getTypeConverter();
        final Term baseHeap = tb.getBaseHeap();
        final Term nullTerm = tb.NULL();

        // construct free preconditions
        final Term wellFormed = tb.wellFormed(baseHeap);
        final Term nonNull = tb.not(tb.equals(thread, nullTerm));
        final Term created = tb.created(thread);
        final Term exactInstance = tb.exactInstance(threadType.getSort(), thread);
        final Sort runnableSort = target.sort();
        final Function targetField = tc.getHeapLDT().getFieldSymbolForPV(target, environmentServices);
        final Term selectTarget = tb.select(runnableSort, baseHeap, thread, tb.func(targetField));
        final Term t = tb.func(new Function(new Name("runner"), runnableSort));
        final Term targetDef = tb.equals(selectTarget, t);
        final Term tNonNull = tb.not(tb.equals(t, nullTerm));
        final Term tCreated = tb.created(t);
        // TODO: exact instance?

        return tb.and(wellFormed, nonNull, created, exactInstance, targetDef, tNonNull, tCreated);
    }

    private JavaBlock buildJavaBlock(final ProgramVariable threadVar,
                                     final KeYJavaType threadType,
                                     final LocationVariable target) {
        final ReferencePrefix reference = KeYJavaASTFactory.fieldReference(threadVar, target);
        final MethodReference runMethod =
                KeYJavaASTFactory.methodCall(reference, RUN, new ImmutableArray<Expression>());
        // TODO: further technical setup
        final de.uka.ilkd.key.java.statement.Try tryCatch =
                KeYJavaASTFactory.tryBlock(
                        KeYJavaASTFactory.block(runMethod),
                        new Branch[] {
                            KeYJavaASTFactory.catchClause(javaInfo, "e", "Throwable", KeYJavaASTFactory.block())});
        final ExecutionContext ec =
                KeYJavaASTFactory.executionContext(threadType, null, threadVar, threadType);
        final StatementBlock block = KeYJavaASTFactory.block(tryCatch);
        final MethodFrame mf = KeYJavaASTFactory.methodFrame(ec, block);

        return JavaBlock.createJavaBlock(mf);
    }

    private Term buildFrame(final Term thread,
                            final Term heaps,
                            final Term prevHeap,
                            final Term currHeap) {
        final Sort fieldSort = heapLDT.getFieldSort();
        final Sort objectSort = javaInfo.objectSort();

        final QuantifiableVariable fVar = new LogicVariable(new Name("f"), fieldSort);
        final QuantifiableVariable oVar = new LogicVariable(new Name("o"), objectSort);
        final Term f = tb.var(fVar);
        final Term o = tb.var(oVar);

        final Term notChanged = tspec.getNotChanged(thread, environmentServices);
        final Term changeLocal = tspec.getAssignable(thread, environmentServices);
        final Term changeRemote = tb.setMinus(tb.allLocs(), notChanged);
        final Term inSet = tb.elementOf(o, f, tb.union(changeRemote, changeLocal));

        final Term select0 = tb.select(Sort.ANY, prevHeap, o, f);
        final Term select1 = tb.select(Sort.ANY, currHeap, o, f);
        final Term equalSelect = tb.equals(select0, select1);

        return tb.all(oVar, tb.all(fVar, tb.or(inSet, equalSelect)));
    }

    private Term buildTraceProp(final Term thread, final Term heaps) {
        final TypeConverter tc = environmentServices.getTypeConverter();

        final Sort heapSort = heapLDT.targetSort();
        final IntegerLDT integerLDT = tc.getIntegerLDT();
        final Sort intSort = integerLDT.targetSort();

        final QuantifiableVariable iVar = new LogicVariable(new Name("i"), intSort);
        final Term idx = tb.var(iVar);

        final Term prevHeap = tb.seqGet(heapSort, heaps, tb.sub(idx, tb.one()));
        final Term currHeap = tb.seqGet(heapSort, heaps, idx);

        final Term guard = tb.and(tb.lt(tb.zero(), idx), tb.lt(idx, tb.seqLen(heaps)));
        final Term frame = buildFrame(thread, heaps, prevHeap, currHeap);
        final Term guar = tspec.getGuarantee(prevHeap, currHeap, thread, environmentServices);

        return tb.all(iVar, tb.imp(guard, tb.and(frame, guar)));
    }

    private Term buildGuaranteeTerm(final ProgramVariable threadVar,
                                    final KeYJavaType threadType,
                                    final LocationVariable target) {
        final TypeConverter tc = environmentServices.getTypeConverter();
        final Term baseHeap = tb.getBaseHeap();

        final Term thread = tb.var(threadVar);
        final Term heaps = tb.var(tc.getSeqLDT().getHeapSeq());

        final JavaBlock jb = buildJavaBlock(threadVar, threadType, target);

        final Term traceProp = buildTraceProp(thread, heaps);

        final Modality modality = Modality.DIA; // XXX: only diamond for uniform translation

        final Term pre = tspec.getPre(baseHeap, thread, environmentServices);
        final Term upd = tb.elementary(heaps, tb.seqSingleton(baseHeap));
        final Term prog = tb.prog(modality, jb, traceProp);

        return tb.imp(pre, tb.apply(upd, prog));
    }

    private Term buildReflexivityAndTransitivityTerm(final Term thread) {
        final Sort heapSort = heapLDT.targetSort();

        // reflexivity / transitivity
        final QuantifiableVariable heap0Var = new LogicVariable(new Name("heap_0"),heapSort);
        final QuantifiableVariable heap1Var = new LogicVariable(new Name("heap_1"),heapSort);
        final QuantifiableVariable heap2Var = new LogicVariable(new Name("heap_2"),heapSort);
        final ArrayList<QuantifiableVariable> vars = new ArrayList<QuantifiableVariable>(3);

        vars.add(heap0Var);
        vars.add(heap1Var);
        vars.add(heap2Var);
        
        final Term heap0 = tb.var(heap0Var);
        final Term heap1 = tb.var(heap1Var);
        final Term heap2 = tb.var(heap2Var);

        final Term relyTrans0 = tspec.getRely(heap0, heap1, thread, environmentServices);
        final Term relyTrans1 = tspec.getRely(heap1, heap2, thread, environmentServices);
        final Term relyTrans2 = tspec.getRely(heap0, heap2, thread, environmentServices);

        final Term trans = tb.imp(tb.and(relyTrans0,relyTrans1), relyTrans2);
        final Term reflex = tspec.getRely(heap0, heap0, thread, environmentServices);
        
        return tb.all(vars, tb.and(reflex, trans));
    }

    @Override
    public void readProblem() throws ProofInputException {
        final KeYJavaType threadType = tspec.getKJT();
        final ProgramVariable threadVar = tspec.getThreadVar();
        register(threadVar, environmentServices);
        final Term thread = tb.var(threadVar);
        final LocationVariable target = (LocationVariable) javaInfo.getAttributeSuper("target", threadType);

        final Term guaranteeTerm = buildGuaranteeTerm(threadVar, threadType, target);
        final Term transitivityTerm = buildReflexivityAndTransitivityTerm(thread);
        final Term freePre = buildFreePre(thread, threadType, target);

        final Term result = tb.imp(freePre, tb.and(guaranteeTerm, transitivityTerm));

        assignPOTerms(result);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
        super.fillSaveProperties(properties);
        properties.setProperty("threadSpec", tspec.getName());
    }

    /**
     * Instantiates a new proof obligation with the given settings.
     * @param initConfig The already load {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     * @throws IOException Occurred Exception.
     */
    public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) throws IOException {
        String tSpecName = properties.getProperty("threadSpec");
        final DisplayableSpecificationElement contract =
                initConfig.getServices().getSpecificationRepository().getContractByName(tSpecName);
        if (contract == null) {
            throw new RuntimeException("Contract not found: " + tSpecName);
        }
        else {
            final ProofOblInput po = contract.createProofObl(initConfig);
            return new LoadedPOContainer(po);
        }
    }
}