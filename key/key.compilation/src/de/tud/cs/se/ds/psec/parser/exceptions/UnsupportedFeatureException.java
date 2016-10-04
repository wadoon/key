package de.tud.cs.se.ds.psec.parser.exceptions;

/**
 * {@link RuntimeException} being thrown during an attempt to use a bytecode
 * feature that is currently not supported, e.g. floating point arithmetic.
 *
 * @author Dominic Scheurer
 */
@SuppressWarnings("serial")
public class UnsupportedFeatureException extends RuntimeException {

    /**
     * @see Exception#Exception()
     */
    public UnsupportedFeatureException() {
        super();
    }

    /**
     * @see Exception#Exception(String)
     */
    public UnsupportedFeatureException(String message) {
        super(message);
    }

    /**
     * @see Exception#Exception(String, Throwable)
     */
    public UnsupportedFeatureException(String message, Throwable cause) {
        super(message, cause);
    }

}
