package edu.kit.iti.formal.psdbg.interpreter.dbg;

import edu.kit.iti.formal.psdbg.interpreter.Interpreter;

/**
 * @author Alexander Weigl
 * @version 1 (30.07.19)
 */
public interface HaltListener {
    <T> void onContinue(Interpreter<T> interpreter);

    <T> void onHalt(Interpreter<T> interpreter);
}
