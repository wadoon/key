package keyext.extract_preconditions;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.*;

/**
 * Strategy which does nothing, but applying One Step Simplifications
 */
public class SimplifierStrategy implements Strategy {

    @Override
    public Name name() {
        return new Name("Simplifier Strategy");
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {

        if (app.rule() instanceof OneStepSimplifier) {
            return NumberRuleAppCost.getZeroCost();
        }

        return TopRuleAppCost.INSTANCE;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {

        return app.rule() instanceof OneStepSimplifier;

    }

    @Override
    public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                               RuleAppCostCollector collector) {
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }

}