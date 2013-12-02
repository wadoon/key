package com.csvanefalk.keytestgen.core.concurrency.capsules;

import java.util.concurrent.CountDownLatch;

public class LaunchContainer implements Runnable {

    /**
     * Used for synchronization of containers controlled by the same container.
     */
    private CountDownLatch latch;

    private final ICapsule wrappedCapsule;

    public LaunchContainer(final ICapsule wrappedCapsule) {
        super();
        this.wrappedCapsule = wrappedCapsule;
    }

    public ICapsule getWrappedCapsule() {
        return wrappedCapsule;
    }

    @Override
    public final void run() {
        try {
            wrappedCapsule.doWork();
        } finally {
            if (latch != null) {
                latch.countDown();
            }
        }
    }

    public void setLatch(final CountDownLatch latch2) {
        latch = latch2;
    }

    public void stop() {
        wrappedCapsule.terminate();
        if (latch != null) {
            latch.countDown();
        }
    }
}
