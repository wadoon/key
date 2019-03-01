package edu.kit.iti.formal.psdbg.interpreter.funchdl;

import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;

import javax.annotation.Nullable;
import java.util.Collections;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.17)
 */
public interface CommandHandler<T> {
    /**
     * determines if this handler can handle the given command
     *
     * @param call
     * @return
     * @throws IllegalArgumentException
     */
    boolean handles(CallStatement call, @Nullable T data) throws IllegalArgumentException;

    /**
     * @param interpreter
     * @param call
     * @param params
     * @param data
     */
    void evaluate(Interpreter<T> interpreter,
                  CallStatement call,
                  VariableAssignment params, T data);

    default boolean isAtomic() {
        return true;
    }

    /**
     * Return a html documentation message
     *
     * @param call
     * @return
     */
    default String getHelp(CallStatement call) {
        return "Help is not implemented for " + getClass().getCanonicalName();
    }

    default Stream<String> getArguments(String name) {
        return Stream.of();
    }

    default boolean isUninterpretedParams(CallStatement call){
        return false;
    }
}
