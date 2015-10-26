package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopInvariant;

public class ReattachLoopInvariant extends ProgramTransformer {

    public ReattachLoopInvariant(LoopStatement ls) {
        super("#reattachLoopInvariant", ls);
    }

    @Override
    public ProgramElement transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {

        final ProgramElement context = svInst.getContextInstantiation().contextProgram();
        
        if (context != null) {
            assert PosInProgram.getProgramAt(svInst.getContextInstantiation().getInstantiation().prefix(), context) instanceof LoopStatement;
            LoopStatement loop = (LoopStatement) 
                    PosInProgram.getProgramAt(svInst.getContextInstantiation().getInstantiation().prefix(), context);
            
            LoopInvariant li = services.getSpecificationRepository().getLoopInvariant(loop);
            if (li != null) {
                li = li.setLoop((While)pe);
                services.getSpecificationRepository().addLoopInvariant(li);
            }
        }        
        return pe;
    }

}
