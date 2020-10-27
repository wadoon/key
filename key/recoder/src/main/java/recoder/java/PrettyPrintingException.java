package recoder.java;

import java.io.IOException;

public class PrettyPrintingException extends RuntimeException {
    private static final long serialVersionUID = -4300469088231850754L;

    private final IOException ioe;

    public PrettyPrintingException(IOException ioe) {
        this.ioe = ioe;
    }

    public IOException getWrappedException() {
        return this.ioe;
    }

    public String toString() {
        return this.ioe.toString();
    }
}
