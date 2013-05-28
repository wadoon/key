package se.gu.svanefalk.testgeneration.core.concurrency.capsules;

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
public class CapsuleExecutor {

    private static CapsuleExecutor instance = null;

    public static CapsuleExecutor getInstance() {
        if (CapsuleExecutor.instance == null) {
            CapsuleExecutor.instance = new CapsuleExecutor();
        }
        return CapsuleExecutor.instance;
    }

    private final Executor executor = Executors.newCachedThreadPool();

    private CapsuleExecutor() {
    }

    /**
     * Execute one or more {@link AbstractCapsule} instances, and block until they
     * finish executing.
     * 
     * @param runnables
     *            the runnables
     */
    public void executeCapsulesAndWait(final List<? extends AbstractCapsule> capsules) {

        /*
         * Setup and launch capsules
         */
        final CountDownLatch latch = new CountDownLatch(capsules.size());
        for (final AbstractCapsule capsule : capsules) {
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