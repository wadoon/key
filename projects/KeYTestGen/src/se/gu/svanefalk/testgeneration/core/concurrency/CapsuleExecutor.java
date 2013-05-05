package se.gu.svanefalk.testgeneration.core.concurrency;

import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Executor;
import java.util.concurrent.Executors;

/**
 * Encapsulates an {@link Executor} for global use across KeYTestGen2.
 * 
 * @author christopher
 * 
 */
public enum CapsuleExecutor {
    INSTANCE;

    private final Executor executor = Executors.newCachedThreadPool();

    /**
     * Execute one or more {@link Capsule} instances, and block until they
     * finish executing.
     * 
     * @param runnables
     *            the runnables
     */
    public void executeCapsulesAndWait(final List<? extends Capsule> capsules) {

        /*
         * Setup and launch capsules
         */
        final CountDownLatch latch = new CountDownLatch(capsules.size());
        for (final Capsule capsule : capsules) {
            capsule.setLatch(latch);
            executor.execute(capsule);
        }

        /*
         * Wait for the capsules to finish
         */
        while (true) {
            try {
                latch.await();
                break;
            } catch (final InterruptedException e) {
                continue;
            }
        }
    }
}