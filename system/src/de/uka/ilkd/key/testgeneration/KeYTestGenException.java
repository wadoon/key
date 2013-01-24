package de.uka.ilkd.key.testgeneration;

/**
 * Default supertype for all exceptions that can be thrown from any module in
 * KeYTestGen.
 * 
 * @author christopher
 */
public class KeYTestGenException extends Exception {
    private static final long serialVersionUID = -4916814485272872541L;

    public KeYTestGenException(String message) {
        super(message);
    }

    public KeYTestGenException(String message, Throwable cause) {
        super(message, cause);
    }
}
