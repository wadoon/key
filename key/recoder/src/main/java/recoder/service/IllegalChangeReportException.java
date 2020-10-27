package recoder.service;

public class IllegalChangeReportException extends RuntimeException {
    private static final long serialVersionUID = 1930002520114622048L;

    public IllegalChangeReportException() {
    }

    public IllegalChangeReportException(String msg) {
        super(msg);
    }
}
