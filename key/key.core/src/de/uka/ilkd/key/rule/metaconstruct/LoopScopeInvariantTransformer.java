package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class LoopScopeInvariantTransformer extends ProgramTransformer {

    public LoopScopeInvariantTransformer(LoopStatement loop) {
        super("loopScopeInvariantTransformer", loop);
    } 

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        Term invariant = services.getSpecificationRepository().getLoopSpec((LoopStatement) pe).getInvariant(services);
        System.out.println(invariant.toString());
        
        return null;
    }

}
