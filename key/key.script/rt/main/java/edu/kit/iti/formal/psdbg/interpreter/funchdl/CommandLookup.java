package edu.kit.iti.formal.psdbg.interpreter.funchdl;

import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.17)
 */
public interface CommandLookup<T> {
    void callCommand(Interpreter<T> i, CallStatement c, VariableAssignment p);

    boolean isAtomic(CallStatement call);

    public CommandHandler<T> getBuilder(CallStatement callStatement, T data);

    String getHelp(CallStatement call);

    default boolean isUninterpretedParams(CallStatement call){
        return false;
    }
}
