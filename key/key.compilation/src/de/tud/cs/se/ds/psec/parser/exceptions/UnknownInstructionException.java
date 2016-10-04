package de.tud.cs.se.ds.psec.parser.exceptions;

/**
 * {@link RuntimeException} being thrown during an attempt to use a bytecode
 * Instruction which is currently unknown.
 *
 * @author Dominic Scheurer
 */
@SuppressWarnings("serial")
public class UnknownInstructionException extends RuntimeException {

    /**
     * @see Exception#Exception()
     */
    public UnknownInstructionException() {
        super();
    }

    /**
     * @see Exception#Exception(String)
     */
    public UnknownInstructionException(String message) {
        super(message);
    }

    /**
     * @see Exception#Exception(String, Throwable)
     */
    public UnknownInstructionException(String message, Throwable cause) {
        super(message, cause);
    }

}
