package de.uka.ilkd.key.proof.init;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Properties;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.ThreadSpecification;


public class GuaranteePO extends AbstractRelyGuaranteePO {
    
    private final static String NAME = ".Thread Specification";
    private final static String RUN = "run";
    
    private final TermBuilder tb; 
    
    public GuaranteePO (InitConfig initConfig, ThreadSpecification tspec) {
        super(initConfig, tspec.getKJT()+NAME, tspec);
        tb = environmentServices.getTermBuilder();
    }

    @Override
    public void readProblem() throws ProofInputException {

        // guarantee term
        final Sort heapSort = heapLDT.targetSort();
        final Sort fieldSort = heapLDT.getFieldSort();
        final Sort objectSort = javaInfo.objectSort();
        final TypeConverter typeConverter = environmentServices.getTypeConverter();
        final IntegerLDT integerLDT = typeConverter.getIntegerLDT();
        final Sort intSort = integerLDT.targetSort();
        
        final ProgramVariable threadVar = tb.selfVar(tspec.getKJT(), true);
        register(threadVar, environmentServices);
        final Term thread = tb.var(threadVar);
        final ProgramVariable heapsVar = typeConverter.getSeqLDT().getHeapSeq();
        final Term heaps = tb.var(heapsVar);
        
        final LocationVariable target = (LocationVariable) javaInfo.getAttributeSuper("target", tspec.getKJT());
        final ReferencePrefix reference = KeYJavaASTFactory.fieldReference(threadVar, target);
        final MethodReference runMethod = KeYJavaASTFactory.methodCall(reference, RUN, new ImmutableArray<Expression>());
        // TODO: further technical setup
        final de.uka.ilkd.key.java.statement.Try tryCatch = KeYJavaASTFactory.tryBlock(KeYJavaASTFactory.block(runMethod), 
                        new Branch[]{KeYJavaASTFactory.catchClause(javaInfo, "e", "Throwable", KeYJavaASTFactory.block())});
        final JavaBlock jb = JavaBlock.createJavaBlock(KeYJavaASTFactory.block(tryCatch));
        
        final QuantifiableVariable iVar = new LogicVariable(new Name("i"), intSort);
        final Term idx = tb.var(iVar);
        

        final Term prevHeap = tb.seqGet(heapSort, heaps, tb.sub(idx, tb.one()));
        final Term currHeap = tb.seqGet(heapSort, heaps, idx);
        
        final QuantifiableVariable fVar = new LogicVariable(new Name("f"), fieldSort);
        final QuantifiableVariable oVar = new LogicVariable(new Name("o"), objectSort);
        final Term f = tb.var(fVar);
        final Term o = tb.var(oVar);
        final Term select0 = tb.select(Sort.ANY, prevHeap, o, f);
        final Term select1 = tb.select(Sort.ANY, currHeap, o, f);
        final Term equalSelect = tb.equals(select0, select1);
        
        final Term notChanged = tspec.getNotChanged(thread, environmentServices);
        final Term changeLocal = tspec.getAssignable(thread, environmentServices);
        final Term changeRemote = tb.setMinus(tb.allLocs(), notChanged);
        final Term inSet = tb.elementOf(o, f, tb.union(changeRemote, changeLocal));
        final Term frame = tb.all(oVar, tb.all(fVar, tb.or(inSet, equalSelect)));
        
        final Term guar = tspec.getGuarantee(prevHeap, currHeap, thread, environmentServices);
        final Term guard = tb.and(tb.lt(tb.zero(), idx), tb.lt(idx, tb.seqLen(heaps)));
        final Term traceProp = tb.all(iVar, tb.imp(guard, tb.and(frame,guar)));
        
        final Modality modality = Modality.DIA; // XXX: only diamond for uniform translation
        final Term prog = tb.prog(modality, jb, traceProp);
        final Term upd = tb.elementary(tb.var(heapsVar), tb.seqSingleton(tb.getBaseHeap()));
        
        final Term guaranteeTerm = tb.apply(upd, prog);
    
    
        // reflexivity / transitivity
        final QuantifiableVariable heap0Var = new LogicVariable(new Name("heap_0"),heapSort);
        final QuantifiableVariable heap1Var = new LogicVariable(new Name("heap_1"),heapSort);
        final QuantifiableVariable heap2Var = new LogicVariable(new Name("heap_2"),heapSort);
        final ArrayList<QuantifiableVariable> vars = new ArrayList<QuantifiableVariable>(3);
        vars.add(heap0Var); vars.add(heap1Var); vars.add(heap2Var);
        
        final Term heap0 = tb.var(heap0Var);
        final Term heap1 = tb.var(heap1Var);
        final Term heap2 = tb.var(heap2Var);

        final Term relyTrans0 = tspec.getRely(heap0, heap1, thread, environmentServices);
        final Term relyTrans1 = tspec.getRely(heap1, heap2, thread, environmentServices);
        final Term relyTrans2 = tspec.getRely(heap0, heap2, thread, environmentServices);
        final Term trans = tb.imp(tb.and(relyTrans0,relyTrans1), relyTrans2);
        
        final Term reflex = tspec.getRely(heap0, heap0, thread, environmentServices);
        
        final Term transitivityTerm = tb.all(vars, tb.and(reflex, trans));
        

        // construct free preconditions
        final Term wellFormed = tb.wellFormed(tb.getBaseHeap());
        final Term nonNull = tb.not(tb.equals(thread, tb.NULL()));
        final Term created = tb.created(thread);
        final Term exactInstance = tb.exactInstance(tspec.getKJT().getSort(), thread);
        final Sort runnableSort = target.sort();
        final Function targetField =  typeConverter.getHeapLDT().getFieldSymbolForPV(target, environmentServices);
        final Term selectTarget = tb.select(runnableSort, tb.getBaseHeap(), thread, tb.func(targetField));
        final Term t = tb.func(new Function(new Name("runner"), runnableSort));
        final Term targetDef = tb.equals(selectTarget, t);
        
        final Term freePre = tb.and(wellFormed, nonNull, created, exactInstance, targetDef);
        
        final Term result = tb.imp(freePre, tb.and(guaranteeTerm, transitivityTerm));
       
        assignPOTerms(result);
    }
    
    /**
     * Instantiates a new proof obligation with the given settings.
     * @param initConfig The already load {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     * @throws IOException Occurred Exception.
     */
    public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties)
          throws IOException {
        // TODO
        throw new Error("not implemented");
    }
    
}
