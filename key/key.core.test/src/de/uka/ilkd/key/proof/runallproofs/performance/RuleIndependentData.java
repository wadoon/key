package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.Properties;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;

/**
 * The purpose of this class is to write rule-independent data to the
 * filesystem, that is obtained from a {@link DataRecordingStrategy} run.
 */
public class RuleIndependentData {

    private static final String APPLY_STRATEGY_DURATION = "applyStrategyDuration";

    private final File ruleIndependentDataLocation = new File(
            RunAllProofsTestWithComputeCostProfiling.PROFILING_DIR,
            "ruleIndependentData.properties");

    private final Properties ruleIndependentData = new Properties();

    private RuleIndependentData() {
        /*
         * Load previous rule independent data from file, if it exists.
         */
        if (ruleIndependentDataLocation.exists()) {
            try (Reader r = new FileReader(ruleIndependentDataLocation)) {
                ruleIndependentData.load(r);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }

    private long get(String key) {
        return Long.parseLong(ruleIndependentData.getProperty(key, 0 + ""));
    }

    private void add(String key, long l) {
        long value = get(key);
        value += l;
        ruleIndependentData.setProperty(key, value + "");
    }

    private void addTotalDurationAndInvocations(String functionName,
            FunctionPerformanceData data) {
        add(functionName + "Invocations", data.totalInvocations);
        add(functionName + "Duration", data.totalDuration);
    }

    private void updateDataOnFileSystem() {
        /*
         * Update duration percentage for functions computeCost() and
         * instantiateApp().
         */
        final int ccPercentage = updateFunctionPercentage("computeCost");
        final int iaPercentage = updateFunctionPercentage("instantiateApp");

        /*
         * Update data in file: ruleIndependentData.properties
         */
        try (FileOutputStream ruleIndependentDataStream = new FileOutputStream(
                ruleIndependentDataLocation);) {
            ruleIndependentData.store(ruleIndependentDataStream,
                    "Performance Test Total Durations (and Invocations)");
        } catch (Exception e) {
            throw new RuntimeException(e);
        }

        /*
         * Update data in file: PercentageOverTime.data
         */
        File percentageOverTimeFile = new File(
                RunAllProofsTest.RUNALLPROOFS_DIR, "PercentageOverTime.data");
        try (DataRecordingTable table = new DataRecordingTable(
                percentageOverTimeFile, new String[] {
                        "System.currentTimeMillis()", "computeCostPercentage",
                        "instantiateAppPercentage" },
                "Percentages of how much time computeCost() and instantiateApp() take "
                        + "in overall applyStrategy() execution.");) {
            table.writeRow(new Object[] { System.currentTimeMillis(),
                    ccPercentage, iaPercentage });
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Computes how much time a profiled function takes from overall
     * applyStrategy() time.
     */
    private int updateFunctionPercentage(String functionName) {
        double a = get(functionName + "Duration");
        double b = get(APPLY_STRATEGY_DURATION);
        String key = functionName + "Duration_PERCENTAGE";
        int percentage = (int) (100 * a / b);
        ruleIndependentData.setProperty(key, percentage + "%");
        return percentage;
    }

    /**
     * Updates {@link RuleIndependentData} after by adding data obtained from
     * {@link DataRecordingStrategy}.
     */
    public static void update(long applyStrategyDuration,
            DataRecordingStrategy dataRecordingStrategy) {
        RuleIndependentData t = new RuleIndependentData();

        t.add("applyStrategyInvocations", 1);
        t.add(APPLY_STRATEGY_DURATION, applyStrategyDuration);

        t.addTotalDurationAndInvocations("computeCost",
                dataRecordingStrategy.computeCostData);
        t.addTotalDurationAndInvocations("instantiateApp",
                dataRecordingStrategy.instantiateAppData);

        t.updateDataOnFileSystem();
    }

}
