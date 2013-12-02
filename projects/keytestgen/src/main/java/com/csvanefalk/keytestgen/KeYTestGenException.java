package com.csvanefalk.keytestgen;

/**
 * Default supertype for all exceptions that can be thrown from any module in
 * KeYTestGen.
 *
 * @author christopher
 */
public class KeYTestGenException extends Exception {
    private static final long serialVersionUID = -4916814485272872541L;

    public KeYTestGenException(final String message) {
        super(message);
    }

    public KeYTestGenException(final String message, final Throwable cause) {
        super(message, cause);
    }
}
