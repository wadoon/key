package se.gu.svanefalk.testgeneration.core.concurrency;

import java.util.concurrent.CountDownLatch;

import se.gu.svanefalk.testgeneration.KeYTestGenException;

/**
 * Capsules represent autonomous units of functionality within the KeYTestGen2
 * core, meant to make it easy for the system as a whole to run concurrently.
 * 
 * @author christopher
 * 
 */
public abstract class Capsule implements Runnable {

    private CountDownLatch latch;

    /**
     * Flag to indicate whether or not the outcome of this capsules execution
     * was succesful or not.
     */
    private boolean succeeded = false;

    /**
     * Exception potentially thrown during the execution of this Capsule.
     */
    private KeYTestGenException thrownException;

    public abstract void doWork();

    /**
     * @return the exception thrown during the execution of this capsule, if
     *         any.
     */
    public KeYTestGenException getThrownException() {
        return thrownException;
    }

    /**
     * @return true if the Capsule executed succesfully, false otherwise.
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
     * Indicate that the execution of the the Capsule succeeded. Cannot be
     * reveresed once set due to the nature of the Capsule itself.
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
}