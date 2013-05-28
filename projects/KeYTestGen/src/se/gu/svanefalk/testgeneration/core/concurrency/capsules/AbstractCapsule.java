package se.gu.svanefalk.testgeneration.core.concurrency.capsules;

import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.CountDownLatch;

import se.gu.svanefalk.testgeneration.KeYTestGenException;
import se.gu.svanefalk.testgeneration.core.concurrency.monitor.ICapsuleMonitor;
import se.gu.svanefalk.testgeneration.core.concurrency.monitor.IMonitorEvent;

/**
 * Capsules represent autonomous units of functionality within the KeYTestGen2
 * core, meant to make it easy for the system as a whole to run concurrently.
 * 
 * @author christopher
 * 
 */
public abstract class AbstractCapsule implements ICapsule {

    /**
     * Latch used for the purposeo synchronizing several capsules of the same
     * type.
     */
    private CountDownLatch latch;

    /**
     * Monitors for this capsule.
     */
    private final List<ICapsuleMonitor> monitors = new LinkedList<>();

    /**
     * Flag to indicate whether or not the outcome of this capsules execution
     * was succesful or not.
     */
    private boolean succeeded = false;

    /**
     * Exception potentially thrown during the execution of this
     * AbstractCapsule.
     */
    private KeYTestGenException thrownException;

    /**
     * @return the exception thrown during the execution of this capsule, if
     *         any.
     */
    public KeYTestGenException getThrownException() {
        return thrownException;
    }

    /**
     * @return true if the AbstractCapsule executed succesfully, false
     *         otherwise.
     */
    public boolean isSucceeded() {
        return succeeded;
    }

    @Override
    public final void run() {
        try {
            doWork();
        } finally {
            latch.countDown();
        }
    }

    /**
     * @param latch
     *            the latch to set
     */
    void setLatch(final CountDownLatch latch) {
        this.latch = latch;
    }

    /**
     * Indicate that the execution of the the AbstractCapsule succeeded. Cannot
     * be reveresed once set due to the nature of the AbstractCapsule itself.
     */
    protected void setSucceeded() {
        succeeded = true;
    }

    /**
     * @param thrownException
     *            the thrownException to set
     */
    protected void setThrownException(final KeYTestGenException thrownException) {
        this.thrownException = thrownException;
    }

    public void addMonitor(ICapsuleMonitor capsuleMonitor) {
        monitors.add(capsuleMonitor);
    }

    protected void notifyMonitors(IMonitorEvent event) {
        for (ICapsuleMonitor monitor : monitors) {
            monitor.doNotify(this, event);
        }
    }
}