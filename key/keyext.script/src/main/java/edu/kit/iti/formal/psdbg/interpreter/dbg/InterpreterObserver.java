package edu.kit.iti.formal.psdbg.interpreter.dbg;

import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.parser.Visitor;

import javax.annotation.Nonnull;

/**
 * Helper interface for classes whom wants to listen on a single interpreter instance.
 *
 * @author Alexander Weigl
 * @version 1 (27.10.17)
 */
public interface InterpreterObserver<T> {
    default void install(@Nonnull Interpreter<T> interpreter) {
        if (getInterpreter() != null) deinstall(interpreter);
        interpreter.getEntryListeners().add(0, getEntryListener());
        interpreter.getExitListeners().add(0, getExitListener());
        setInterpreter(interpreter);
    }

    Interpreter<T> getInterpreter();

    void setInterpreter(Interpreter<T> interpreter);

    default void deinstall(@Nonnull Interpreter<T> interpreter) {
        if (interpreter != null) {
            interpreter.getEntryListeners().remove(getEntryListener());
            interpreter.getExitListeners().remove(getExitListener());
        }
    }

    Visitor getExitListener();

    Visitor getEntryListener();
}
