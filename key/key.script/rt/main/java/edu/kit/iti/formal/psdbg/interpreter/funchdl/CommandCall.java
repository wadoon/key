package edu.kit.iti.formal.psdbg.interpreter.funchdl;

import edu.kit.iti.formal.psdbg.interpreter.Interpreter;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.17)
 */
public interface CommandCall {
    void evaluate(Interpreter state);
}
