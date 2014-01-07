package com.csvanefalk.keytestgen.core.concurrency.capsules;

import java.util.Collection;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Executor;
import java.util.concurrent.Executors;

/**
 * Encapsulates an {@link Executor} for global use across KeYTestGen2.
 *
 * @author christopher
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

    public void execute(final List<LaunchContainer> capsules) {
        for (final LaunchContainer capsule : capsules) {
            executor.execute(capsule);
        }
    }

    /**
     * Execute one or more {@link AbstractCapsule} instances, and block until
     * they finish executing.
     *
     * @param containers the runnables
     */
    public void executeCapsulesAndWait(final Collection<? extends LaunchContainer> containers) {

        /*
         * Setup and launch capsules
         */
        final CountDownLatch latch = new CountDownLatch(containers.size());
        for (final LaunchContainer container : containers) {
            container.setLatch(latch);
            executor.execute(container);
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

    public static void __DEBUG_DISPOSE() {
        instance = null;
    }
}