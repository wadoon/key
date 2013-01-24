package de.uka.ilkd.key.testgeneration.util;

import java.util.Calendar;
import java.util.HashMap;

/**
 * Benchmarking utilities
 * 
 * @author christopher
 */
public class Benchmark {

    private static final HashMap<String, Long> readings = new HashMap<String, Long>();

    public static int[] counters = new int[100];

    private static long stopWatch = 0L;

    public static void resetStopwatch() {
        stopWatch = Calendar.getInstance().getTimeInMillis();
    }

    public static long readStopWatch() {
        return Calendar.getInstance().getTimeInMillis() - stopWatch;
    }

    /**
     * Resets the clock (i.e. sets it to the current time, since all readings
     * are done relative to this).
     */
    public static void startBenchmarking(String event) {

        long clockValue = Calendar.getInstance().getTimeInMillis();
        readings.put(event, clockValue);
    }

    /**
     * Registers the clockValue it took to move from the last clock reading to
     * this event.
     * 
     * @param item
     */
    public static void finishBenchmarking(String event) {

        long clockValue = readings.get(event);
        long finalClockValue = Calendar.getInstance().getTimeInMillis();

        System.out.println("BENCHMARK: " + event + " took " + (finalClockValue - clockValue));
        readings.put(event, finalClockValue - clockValue);
    }

    public static HashMap<String, Long> getReadings() {

        return new HashMap<String, Long>(readings);
    }
}
