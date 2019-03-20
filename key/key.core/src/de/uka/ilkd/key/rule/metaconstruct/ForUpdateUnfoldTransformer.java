package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.ForUpdates;
import de.uka.ilkd.key.java.statement.LoopInit;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
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
public class ForUpdateUnfoldTransformer extends ProgramTransformer {
    /**
     * @param LoopInit
     *            A {@link LoopInit} if called while parsing a taclet.
     */
    public ForUpdateUnfoldTransformer(ForUpdates upd) {
        super("forUpdateUnfoldTransformer", upd);
    }

    /**
     * @param programSV
     *            A {@link ProgramSV} if called while parsing a taclet.
     */
    public ForUpdateUnfoldTransformer(ProgramSV programSV) {
        super("forUpdateUnfoldTransformer", programSV);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        Debug.assertTrue(pe instanceof ForUpdates,
                "ForInitUnfoldTransformer cannot handle ", pe);

        final ForUpdates astUpd = (ForUpdates) pe;
        final Statement[] updStatementList = new Statement[astUpd
                .getExpressionCount()];

        for (int i = 0; i < updStatementList.length; i++) {
            updStatementList[i] = (Statement) astUpd.getExpressionAt(i);
        }

        return updStatementList;
    }
}