package com.csvanefalk.keytestgen.core.concurrency.monitor;

public class CaughtException implements IMonitorEvent<Throwable> {

    private final Throwable thrown;

    public CaughtException(final Throwable thrown) {
        super();
        this.thrown = thrown;
    }

    @Override
    public Throwable getPayload() {
        return thrown;
    }
}
