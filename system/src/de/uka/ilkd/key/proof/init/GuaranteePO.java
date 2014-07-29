package de.uka.ilkd.key.proof.init;

import java.io.IOException;
import java.util.Properties;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.ThreadSpecification;


public class GuaranteePO extends AbstractRelyGuaranteePO {
    
    private static final String RUNNABLE = "java.lang.Runnable";
    private static final ProgramElementName TARGET = new ProgramElementName("target");
    private final static String NAME = "guarantee";
    private final static String RUN = "run";
    
    public GuaranteePO (InitConfig initConfig, ThreadSpecification tspec) {
        super(initConfig, NAME, tspec);
    }

    @Override
    public void readProblem() throws ProofInputException {
        final Sort heapSort = heapLDT.targetSort();
        final Sort fieldSort = heapLDT.getFieldSort();
        final Sort objectSort = javaInfo.objectSort();
        IntegerLDT integerLDT = environmentServices.getTypeConverter().getIntegerLDT();
        final Sort intSort = integerLDT.targetSort();
        final TermBuilder tb = environmentServices.getTermBuilder();
        
        final ProgramVariable threadVar = tb.selfVar(tspec.getKJT(), true);
        register(threadVar, environmentServices);
        final Term thread = tb.var(threadVar);
        final ProgramVariable heapsVar = environmentServices.getTypeConverter().getHeapLDT().getHeapSeq();
        final Term heaps = tb.var(heapsVar);
        
        final KeYJavaType runnableType = javaInfo.getKeYJavaType(RUNNABLE);
        final ProgramVariable target = new LocationVariable(TARGET, runnableType, true);
        final ReferencePrefix reference = KeYJavaASTFactory.fieldReference(threadVar, target);
        final MethodReference runMethod = KeYJavaASTFactory.methodCall(reference, RUN, new ImmutableArray<Expression>());
        // TODO: further technical setup
        final JavaBlock jb = JavaBlock.createJavaBlock(KeYJavaASTFactory.block(runMethod));
        
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
        final Term result = tb.apply(upd, prog);
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
