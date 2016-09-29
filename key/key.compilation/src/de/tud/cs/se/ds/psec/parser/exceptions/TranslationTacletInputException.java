package de.tud.cs.se.ds.psec.parser.exceptions;

/**
 * Reading a translation taclet file failed.
 *
 * @author Dominic Scheurer
 */
@SuppressWarnings("serial")
public class TranslationTacletInputException extends RuntimeException {

    private final String message;

    public TranslationTacletInputException(Exception e) {
        this(e.getMessage(), e);
    }

    public TranslationTacletInputException(String s) {
        this(s, null);
    }

    public TranslationTacletInputException(String message, Throwable cause) {
        this.message = message;
        if (cause != null) {
            initCause(cause);
        }
    }

    @Override
    public String getMessage() {
        return message;
    }

}
