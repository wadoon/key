package se.gu.svanefalk.testgeneration.core.concurrency.capsules;

import java.util.concurrent.CountDownLatch;

public class LaunchContainer implements Runnable {

    /**
     * Used for synchronization of containers controlled by the same container.
     */
    private CountDownLatch latch;

    public LaunchContainer(ICapsule wrappedCapsule) {
        super();
        this.wrappedCapsule = wrappedCapsule;
    }

    private final ICapsule wrappedCapsule;

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

    public void setLatch(CountDownLatch latch2) {
        this.latch = latch2;
    }

    public void stop() {
        wrappedCapsule.terminate();
        if (latch != null) {
            latch.countDown();
        }
    }
}
