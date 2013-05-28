package se.gu.svanefalk.testgeneration.core.concurrency.capsules;

import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.CountDownLatch;

import java_cup.terminal;

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

    private CapsuleController controller;

    /**
     * Indicates if the capsule has been terminated.
     */
    private boolean isTerminated = false;

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
    private Throwable thrownException;

    /**
     * @return the exception thrown during the execution of this capsule, if
     *         any.
     */
    public Throwable getThrownException() {
        return thrownException;
    }

    /**
     * @return true if the AbstractCapsule executed succesfully, false
     *         otherwise.
     */
    public boolean isSucceeded() {
        return succeeded;
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
    protected void setThrownException(final Throwable thrownException) {
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

    @Override
    public void terminate() {
        isTerminated = true;
    }

    @Override
    public void addController(CapsuleController controller) {
        this.controller = controller;
    }

    @Override
    public CapsuleController getController() {
        return controller;
    }

    public boolean isTerminated() {
        return isTerminated;
    }
}