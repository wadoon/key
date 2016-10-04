package de.tud.cs.se.ds.psec.compiler.exceptions;

import de.uka.ilkd.key.rule.Taclet;

/**
 * No translation is known for a given symbolic execution {@link Taclet}.
 *
 * @author Dominic Scheurer
 */
@SuppressWarnings("serial")
public class NoTranslationException extends RuntimeException {

    /**
     * @see Exception#Exception()
     */
    public NoTranslationException() {
        super();
    }

    /**
     * @see Exception#Exception(String)
     */
    public NoTranslationException(String message) {
        super(message);
    }

    /**
     * @see Exception#Exception(String, Throwable)
     */
    public NoTranslationException(String message, Throwable cause) {
        super(message, cause);
    }

}
