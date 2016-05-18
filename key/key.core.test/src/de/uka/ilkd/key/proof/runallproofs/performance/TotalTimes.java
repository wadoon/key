package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Reader;
import java.io.Serializable;
import java.util.Properties;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;

@SuppressWarnings("serial")
public class TotalTimes implements Serializable {

    private static final String APPLY_STRATEGY_DURATION = "applyStrategyDuration";

    private static File ruleIndependentDataLocation = new File(RunAllProofsTest.RUNALLPROOFS_DIR,
            "totaltimes.properties");
    final Properties ruleIndependentData = new Properties();

    TotalTimes() {
        if (ruleIndependentDataLocation.exists()) {
            try {
                try (Reader r = new FileReader(ruleIndependentDataLocation)) {
                    ruleIndependentData.load(r);
                }
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }

    long get(String key) {
        return Long.parseLong(ruleIndependentData.getProperty(key, 0 + ""));
    }

    void add(String key, long l) {
        // System.out.println(key);
        // System.out.println("old: " + get(key));
        // System.out.println("add: " + l);
        long value = get(key);
        value += l;
        ruleIndependentData.setProperty(key, value + "");
        // System.out.println("new: " + get(key));
    }

    void add(String functionName, FunctionPerformanceData data) {
        add(functionName + "Invocations", data.totalInvocations);
        add(functionName + "Duration", data.totalDuration);
    }

    void writeBack() {
        try {
            try (FileOutputStream s = new FileOutputStream(ruleIndependentDataLocation)) {
                int ccPercentage = putFunctionPercentage("computeCost");
                int iaPercentage = putFunctionPercentage("instantiateApp");
                ruleIndependentData.store(s, "Performance Test Total Durations (and Invocations)");
                
                File f = new File(RunAllProofsTest.RUNALLPROOFS_DIR, "PercentageOverTime.data");
                boolean exists = f.exists();
                try (PrintWriter w = new PrintWriter(
                        new FileOutputStream(f, true /* append = true */))) {
                    if(!exists) {
                        w.println("# System.currentTimeMillis() computeCostPercentage instantiateAppPercentage");
                    }
                    w.println(System.currentTimeMillis() + " " + ccPercentage + " " + iaPercentage);
                } catch (FileNotFoundException e) {
                    throw new RuntimeException(e);
                }
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private int putFunctionPercentage(String functionName) {
        double a = get(functionName + "Duration");
        double b = get(APPLY_STRATEGY_DURATION);
        String key = functionName + "Duration_PERCENTAGE";
        int percentage = (int) (100 * a / b);
        ruleIndependentData.setProperty(key, percentage + "%");
        return percentage;
    }

    public static void update(long applyStrategyDuration, DataRecordingStrategy dataRecordingStrategy) {

        TotalTimes t = new TotalTimes();

        t.add("applyStrategyInvocations", 1);
        t.add(APPLY_STRATEGY_DURATION, applyStrategyDuration);

        t.add("computeCost", dataRecordingStrategy.computeCostData);
        t.add("instantiateApp", dataRecordingStrategy.instantiateAppData);

        t.writeBack();

    }

}
