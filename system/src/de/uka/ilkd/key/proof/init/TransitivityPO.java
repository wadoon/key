package de.uka.ilkd.key.proof.init;

import java.util.ArrayList;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.ThreadSpecification;

/**
 * PO for showing that a rely condition is reflexive and transitive.
 * @author bruns
 *
 */
public final class TransitivityPO extends AbstractPO {
    
    private final static String NAME = "Rely Condition is Reflexive/Transitive";
    private final ThreadSpecification rgs;
    
    public TransitivityPO (InitConfig initConfig, ThreadSpecification rgs) {
        super(initConfig, NAME);
        this.rgs = rgs;
    }

    @Override
    public void readProblem() throws ProofInputException {
        final Sort heapSort = environmentServices.getTypeConverter().getHeapLDT().targetSort();
        final TermBuilder tb = environmentServices.getTermBuilder();
        final QuantifiableVariable heap0Var = new LogicVariable(new Name("heap_0"),heapSort);
        final QuantifiableVariable heap1Var = new LogicVariable(new Name("heap_1"),heapSort);
        final QuantifiableVariable heap2Var = new LogicVariable(new Name("heap_2"),heapSort);
        final ArrayList<QuantifiableVariable> vars = new ArrayList<QuantifiableVariable>(3);
        vars.add(heap0Var); vars.add(heap1Var); vars.add(heap2Var);
        
        final ProgramVariable threadVar = tb.selfVar(rgs.getKJT(), true);
        register(threadVar, environmentServices);
        final Term heap0 = tb.var(heap0Var);
        final Term heap1 = tb.var(heap1Var);
        final Term heap2 = tb.var(heap2Var);
        final Term thread = tb.var(threadVar);

        final Term relyTrans0 = rgs.getRely(heap0, heap1, thread, environmentServices);
        final Term relyTrans1 = rgs.getRely(heap1, heap2, thread, environmentServices);
        final Term relyTrans2 = rgs.getRely(heap0, heap2, thread, environmentServices);
        final Term trans = tb.imp(tb.and(relyTrans0,relyTrans1), relyTrans2);
        
        final Term reflex = rgs.getRely(heap0, heap0, thread, environmentServices);
        
        final Term result = tb.all(vars, tb.and(reflex, trans));
        assignPOTerms(result);
    }

    @Override
    protected InitConfig getCreatedInitConfigForSingleProof() {
        return environmentConfig;
    }

}
