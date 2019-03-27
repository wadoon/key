package edu.kit.iti.formal.psdbg.interpreter.exceptions;

import edu.kit.iti.formal.psdbg.parser.ast.Variable;

/**
 * @author Alexander Weigl
 * @version 1 (28.05.17)
 */
public class VariableNotDefinedException extends InterpreterRuntimeException{
    public VariableNotDefinedException() {
        super();
    }

    public VariableNotDefinedException(String message) {
        super(message);
    }

    public VariableNotDefinedException(String message, Throwable cause) {
        super(message, cause);
    }

    public VariableNotDefinedException(Throwable cause) {
        super(cause);
    }

    protected VariableNotDefinedException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }

    public VariableNotDefinedException(Variable name) {
        super(String.format(
                "Variable '%s' (position: %s) is not defined",
                name.getIdentifier(), name.getStartPosition()
        ));

    }
}
