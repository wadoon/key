package de.tud.cs.se.ds.psec.compiler.exceptions;

/**
 * Symbolic execution was not exhaustive; this may be due to an insufficient
 * number of maximum steps, but also due to errors in the program: Then, there
 * may be no applicable execution rule.
 *
 * @author Dominic Scheurer
 */
@SuppressWarnings("serial")
public class IncompleteSymbolicExecutionException extends RuntimeException {

    /**
     * @see Exception#Exception()
     */
    public IncompleteSymbolicExecutionException() {
        super();
    }

    /**
     * @see Exception#Exception(String)
     */
    public IncompleteSymbolicExecutionException(String message) {
        super(message);
    }

    /**
     * @see Exception#Exception(String, Throwable)
     */
    public IncompleteSymbolicExecutionException(String message,
            Throwable cause) {
        super(message, cause);
    }

}
