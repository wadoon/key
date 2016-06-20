package de.uka.ilkd.key.proof.runallproofs.performance;

import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Proof;

class Info {

    final double averageTimeForComputeCost;
    final int computeCostInvocations;
    final ApplyStrategyInfo applyStrategyInfo;
    final Proof proof;

    public Info(ApplyStrategyInfo applyStrategyInfo, int computeCostInvocations, long computeCostTotalTime,
            Proof proof) {
        this.applyStrategyInfo = applyStrategyInfo;
        this.computeCostInvocations = computeCostInvocations;
        this.averageTimeForComputeCost = (double) computeCostTotalTime / (double) computeCostInvocations;
        this.proof = proof;
    }

    String times() {
        return "computeCost total invocations: " + computeCostInvocations + "\n"
                + "Average time for computeCost (in nanoseconds): " + averageTimeForComputeCost;
    }

    public String toString() {
        return times() + "\n\n" + applyStrategyInfo + "\n\n" + proof;
    }

}
