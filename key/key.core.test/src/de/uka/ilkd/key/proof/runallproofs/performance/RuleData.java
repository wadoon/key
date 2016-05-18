package de.uka.ilkd.key.proof.runallproofs.performance;

public class RuleData {

    int numberInvocationsForRule = 1;
    long totalRuleTime;

    public RuleData(long computeCostDuration) {
        this.totalRuleTime = computeCostDuration;
    }

    public void addDuration(long duration) {
        numberInvocationsForRule++;
        totalRuleTime += duration;
    }

}
