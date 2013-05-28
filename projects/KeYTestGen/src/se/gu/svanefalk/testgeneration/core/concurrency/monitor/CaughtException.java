package se.gu.svanefalk.testgeneration.core.concurrency.monitor;

public class CaughtException implements IMonitorEvent<Throwable> {

    public CaughtException(Throwable thrown) {
        super();
        this.thrown = thrown;
    }

    private final Throwable thrown;

    @Override
    public Throwable getPayload() {
        return thrown;
    }
}
