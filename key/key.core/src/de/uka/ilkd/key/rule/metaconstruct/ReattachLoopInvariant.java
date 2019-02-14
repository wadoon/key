package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;

/**
 * Construct for re-attaching a loop invariant that otherwise would get lost
 * after a transformation, for instance, the loop scope-based unwinding rule.
 * Copied from the 2015 TimSort tweaks branch (by DS), original work by Richard.
 *
 * @author Richard Bubel
 */
public class ReattachLoopInvariant extends ProgramTransformer {
    public ReattachLoopInvariant(LoopStatement ls) {
        super("#reattachLoopInvariant", ls);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        final ProgramElement context = //
                svInst.getContextInstantiation().contextProgram();

        if (context != null) {
            final PosInProgram prefix = svInst.getContextInstantiation()
                    .getInstantiation().prefix();

            assert PosInProgram.getProgramAt(prefix,
                    context) instanceof LoopStatement;

            final LoopStatement loop = (LoopStatement) PosInProgram
                    .getProgramAt(prefix, context);
            LoopSpecification li = //
                    services.getSpecificationRepository().getLoopSpec(loop);

            if (li != null) {
                li = li.setLoop((While) pe);
                services.getSpecificationRepository().addLoopInvariant(li);
            }
        }

        return new ProgramElement[] { pe };
    }
}