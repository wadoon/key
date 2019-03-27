package edu.kit.iti.formal.psdbg.interpreter.exceptions;

/**
 * @author Alexander Weigl
 * @version 1 (28.05.17)
 */
public class InterpreterRuntimeException extends RuntimeException {
    public InterpreterRuntimeException() {
        super();
    }

    public InterpreterRuntimeException(String message) {
        super(message);
    }

    public InterpreterRuntimeException(String message, Throwable cause) {
        super(message, cause);
    }

    public InterpreterRuntimeException(Throwable cause) {
        super(cause);
    }

    protected InterpreterRuntimeException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
