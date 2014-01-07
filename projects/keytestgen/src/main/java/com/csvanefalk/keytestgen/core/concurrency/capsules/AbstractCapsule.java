package com.csvanefalk.keytestgen.core.concurrency.capsules;

import com.csvanefalk.keytestgen.core.concurrency.monitor.ICapsuleMonitor;
import com.csvanefalk.keytestgen.core.concurrency.monitor.IMonitorEvent;

import java.util.LinkedList;
import java.util.List;

/**
 * Capsules represent autonomous units of functionality within the KeYTestGen2
 * core, meant to make it easy for the system as a whole to run concurrently.
 *
 * @author christopher
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
    private final List<ICapsuleMonitor> monitors = new LinkedList<ICapsuleMonitor>();

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

    @Override
    public void addController(final CapsuleController controller) {
        this.controller = controller;
    }

    @Override
    public void addMonitor(final ICapsuleMonitor capsuleMonitor) {
        monitors.add(capsuleMonitor);
    }

    @Override
    public CapsuleController getController() {
        return controller;
    }

    /**
     * @return the exception thrown during the execution of this capsule, if
     * any.
     */
    public Throwable getThrownException() {
        return thrownException;
    }

    /**
     * @return true if the AbstractCapsule executed succesfully, false
     * otherwise.
     */
    public boolean isSucceeded() {
        return succeeded;
    }

    public boolean isTerminated() {
        return isTerminated;
    }

    protected void notifyMonitors(final IMonitorEvent event) {
        for (final ICapsuleMonitor monitor : monitors) {
            monitor.doNotify(this, event);
        }
    }

    /**
     * Indicate that the execution of the the AbstractCapsule succeeded. Cannot
     * be reveresed once set due to the nature of the AbstractCapsule itself.
     */
    protected void setSucceeded() {
        succeeded = true;
    }

    /**
     * @param thrownException the thrownException to set
     */
    protected void setThrownException(final Throwable thrownException) {
        this.thrownException = thrownException;
    }

    @Override
    public void terminate() {
        isTerminated = true;
    }
}