package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.IOException;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;

class DataRecordingStrategy extends JavaCardDLStrategy {

    final FunctionPerformanceData computeCostData;
    final FunctionPerformanceData instantiateAppData;

    DataRecordingStrategy(Proof proof, DataRecordingTestFile dataRecordingTestFile) throws IOException {
        super(proof);
        computeCostData = new FunctionPerformanceData(
                RunAllProofsTestWithComputeCostProfiling.computeCostDataDir(dataRecordingTestFile.dataDir),
                dataRecordingTestFile);
        instantiateAppData = new FunctionPerformanceData(
                RunAllProofsTestWithComputeCostProfiling.instantiateAppDataDir(dataRecordingTestFile.dataDir),
                dataRecordingTestFile);
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
        long begin = System.nanoTime();
        RuleAppCost result = super.computeCost(app, pio, goal);
        long end = System.nanoTime();
        computeCostData.addDurationToData(app, goal, end - begin);
        return result;
    }

    @Override
    public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal, RuleAppCostCollector collector) {
        long begin = System.nanoTime();
        super.instantiateApp(app, pio, goal, collector);
        long end = System.nanoTime();
        instantiateAppData.addDurationToData(app, goal, end - begin);
    }

    void saveCollectedData(long applyStrategyDuration) {
        computeCostData.saveCollectedData();
        instantiateAppData.saveCollectedData();
        TotalTimes.update(applyStrategyDuration, this);
    }

}
