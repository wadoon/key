package edu.kit.iti.formal.psdbg.interpreter.exceptions;

/**
 * @author Alexander Weigl
 * @version 1 (23.05.18)
 */
public class InvalidTypeException extends InterpreterRuntimeException{
    public InvalidTypeException() {
        super();
    }

    public InvalidTypeException(String message) {
        super(message);
    }

    public InvalidTypeException(String message, Throwable cause) {
        super(message, cause);
    }

    public InvalidTypeException(Throwable cause) {
        super(cause);
    }

    protected InvalidTypeException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
