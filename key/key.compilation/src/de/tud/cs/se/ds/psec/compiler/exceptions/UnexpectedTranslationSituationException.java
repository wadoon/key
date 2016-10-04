package de.tud.cs.se.ds.psec.compiler.exceptions;

/**
 * During compilation, no or too many translation(s) are applicable for the
 * given situation.
 *
 * @author Dominic Scheurer
 */
@SuppressWarnings("serial")
public class UnexpectedTranslationSituationException extends RuntimeException {

    /**
     * @see Exception#Exception()
     */
    public UnexpectedTranslationSituationException() {
        super();
    }
    
    /**
     * @see Exception#Exception(String)
     */
    public UnexpectedTranslationSituationException(String message) {
        super(message);
    }
    
    /**
     * @see Exception#Exception(String, Throwable)
     */
    public UnexpectedTranslationSituationException(String message, Throwable cause) {
        super(message, cause);
    }
    
}
