package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LoopInit;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.Debug;

/**
 * Pulls the initializor out of a for-loop. Only receives the init as a
 * parameter, not the whole for-loop.
 *
 * Example:
 *
 * \pi for (init; guard; upd) body \omega
 *
 * to:
 *
 * \pi { init' for(; guard; upd) body } \omega
 *
 * @author Benedikt Dreher
 */
public class ForInitUnfoldTransformer extends ProgramTransformer {
    /**
     * @param LoopInit
     *            A {@link LoopInit} if called while parsing a taclet.
     */
    public ForInitUnfoldTransformer(LoopInit loopinit) {
        super("forInitUnfoldTransformer", loopinit);
    }

    /**
     * @param programSV
     *            A {@link ProgramSV} if called while parsing a taclet.
     */
    public ForInitUnfoldTransformer(ProgramSV programSV) {
        super("forInitUnfoldTransformer", programSV);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        Debug.assertTrue(pe instanceof LoopInit,
                "ForInitUnfoldTransformer cannot handle ", pe);

        LoopStatement loop = LoopScopeTools.getLoopFromActiveStatement(svInst,
                services);
        LoopSpecification spec = services.getSpecificationRepository()
                .getLoopSpec(loop);

        final LoopInit astLoopInit = (LoopInit) pe;
        final Statement[] loopInitStatementList = new Statement[astLoopInit
                .getInits().size()];

        for (int i = 0; i < loopInitStatementList.length; i++) {
            loopInitStatementList[i] = astLoopInit.getInits().get(i);
        }

        For forWithoutInit = KeYJavaASTFactory.forLoop(loop.getGuard(),
                loop.getIForUpdates(), loop.getBody());
        spec = spec.setLoop(forWithoutInit);
        services.getSpecificationRepository().addLoopInvariant(spec);

        return loopInitStatementList;
    }
}