package recoder.util;

public final class ProgressListenerManager {
    private final ReuseableProgressEvent progressEvent;

    private final Object source;
    private ProgressListener[] progressListeners = new ProgressListener[0];

    public ProgressListenerManager(Object source) {
        this.source = source;
        this.progressEvent = new ReuseableProgressEvent(source, 0, 0, null);
    }

    public ProgressEvent getLastProgressEvent() {
        return this.progressEvent;
    }

    public void fireProgressEvent(int workCount) {
        int length = this.progressListeners.length;
        if (length > 0) {
            this.progressEvent.setWorkDoneCount(workCount);
            for (int i = 0; i < length; i++)
                this.progressListeners[i].workProgressed(this.progressEvent);
        }
    }

    public void fireProgressEvent(int workCount, Object state) {
        int length = this.progressListeners.length;
        if (length > 0) {
            this.progressEvent.setWorkDoneCount(workCount);
            this.progressEvent.setState(state);
            for (int i = 0; i < length; i++)
                this.progressListeners[i].workProgressed(this.progressEvent);
        }
    }

    public void fireProgressEvent(int workCount, int newMaximum) {
        int length = this.progressListeners.length;
        if (length > 0) {
            this.progressEvent.setWorkDoneCount(workCount);
            this.progressEvent.setWorkToDoCount(newMaximum);
            for (int i = 0; i < length; i++)
                this.progressListeners[i].workProgressed(this.progressEvent);
        }
    }

    public void fireProgressEvent(int workCount, int newMaximum, Object state) {
        int length = this.progressListeners.length;
        if (length > 0) {
            this.progressEvent.setWork(workCount, newMaximum, state);
            for (int i = 0; i < length; i++)
                this.progressListeners[i].workProgressed(this.progressEvent);
        }
    }

    public void addProgressListener(ProgressListener l) {
        synchronized (this.progressListeners) {
            int length = this.progressListeners.length;
            ProgressListener[] newListeners = new ProgressListener[length + 1];
            System.arraycopy(this.progressListeners, 0, newListeners, 0, length);
            newListeners[length] = l;
            this.progressListeners = newListeners;
        }
    }

    public void removeProgressListener(ProgressListener chl) {
        synchronized (this.progressListeners) {
            int length = this.progressListeners.length;
            for (int i = length - 1; i >= 0; i--) {
                if (this.progressListeners[i] == chl) {
                    ProgressListener[] newListeners = new ProgressListener[length - 1];
                    if (i > 0)
                        System.arraycopy(this.progressListeners, 0, newListeners, 0, i);
                    if (i < length - 1)
                        System.arraycopy(this.progressListeners, i + 1, newListeners, i, length - 1 - i);
                    this.progressListeners = newListeners;
                    break;
                }
            }
        }
    }

    private class ReuseableProgressEvent extends ProgressEvent {
        private static final long serialVersionUID = -8120253607435943831L;

        public ReuseableProgressEvent(Object source, int workDone, int workToDo, Object state) {
            super(source, workDone, workToDo, state);
        }
    }
}
