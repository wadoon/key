package de.uka.ilkd.key.proof.runallproofs.performance;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.RuleAppCost;

class ModifiedStrategy extends JavaCardDLStrategy {

    int computeCostInvocations = 0;
    long computeCostTotalTimeNano = 0;
    // long computeCostTotalTimeMilli = 0;

    protected ModifiedStrategy(Proof proof) {
        super(proof);
    }

    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
        computeCostInvocations++;
        long begin = System.nanoTime();
        RuleAppCost result = super.computeCost(app, pio, goal);
        computeCostTotalTimeNano += System.nanoTime() - begin;
        return result;
    }

}
