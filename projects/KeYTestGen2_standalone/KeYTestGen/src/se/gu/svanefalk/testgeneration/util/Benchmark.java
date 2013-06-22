package se.gu.svanefalk.testgeneration.util;

import java.util.Calendar;
import java.util.HashMap;

/**
 * Benchmarking utilities
 * 
 * @author christopher
 */
public class Benchmark {

    private static HashMap<String, Long> readings = new HashMap<String, Long>();

    private static long stopWatch = 0L;

    private static final boolean toggleBenchmark = false;

    private static final boolean verbose = true;

    /**
     * Registers the clockValue it took to move from the last clock reading to
     * this event.
     * 
     * @param item
     */
    public static void finishBenchmarking(final String event) {
        if (Benchmark.toggleBenchmark) {
            final long clockValue = Benchmark.readings.get(event);
            final long finalClockValue = Calendar.getInstance().getTimeInMillis();

            if (Benchmark.verbose) {
                System.out.println("BENCHMARK: " + event + " took "
                        + (finalClockValue - clockValue));
            }

            Benchmark.readings.put(event, finalClockValue - clockValue);
        }
    }

    public static HashMap<String, Long> getReadings() {

        return new HashMap<String, Long>(Benchmark.readings);
    }

    public static long readStopWatch() {
        return Calendar.getInstance().getTimeInMillis() - Benchmark.stopWatch;
    }

    public static void reset() {
        Benchmark.stopWatch = 0L;
        Benchmark.readings = new HashMap<String, Long>();
    }

    public static void resetStopwatch() {
        Benchmark.stopWatch = Calendar.getInstance().getTimeInMillis();
    }

    /**
     * Resets the clock (i.e. sets it to the current time, since all readings
     * are done relative to this).
     */
    public static void startBenchmarking(final String event) {

        if (Benchmark.toggleBenchmark) {
            final long clockValue = Calendar.getInstance().getTimeInMillis();
            Benchmark.readings.put(event, clockValue);
        }
    }
}