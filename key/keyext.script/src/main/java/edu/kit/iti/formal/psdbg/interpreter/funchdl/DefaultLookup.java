package edu.kit.iti.formal.psdbg.interpreter.funchdl;

import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.interpreter.exceptions.NoCallHandlerException;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import lombok.Getter;

import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.17)
 */
public class DefaultLookup<T> implements CommandLookup<T> {
    @Getter
    private final List<CommandHandler<T>> builders = new ArrayList<>(1024);

    public DefaultLookup() {
    }

    public DefaultLookup(CommandHandler<T>... cmdh) {
        builders.addAll(Arrays.asList(cmdh));
    }

    public void callCommand(Interpreter<T> interpreter,
                            CallStatement call,
                            VariableAssignment params) {
        T data = interpreter.getSelectedNode().getData();
        CommandHandler b = getBuilder(call, data);
        b.evaluate(interpreter, call, params, data);
    }


    @Override
    public boolean isAtomic(CallStatement call) {
        try {
            CommandHandler cmdh = getBuilder(call, null);
            if (cmdh != null)
                return cmdh.isAtomic();
            return true;
        } catch (NoCallHandlerException nche) {
            return false;
        }
    }

    private CommandHandler<T> getBuilderImpl(CallStatement callStatement, @Nullable T data) {
        for (CommandHandler<T> b : builders) {
            if (b.handles(callStatement, data)) {
                return b;
            }
        }
        return null;
    }

    @Override
    public CommandHandler<T> getBuilder(CallStatement callStatement, @Nullable  T data) {
        CommandHandler<T> found = getBuilderImpl(callStatement, data);
        if (found == null && callStatement.getCommand().contains("_")) {
            //if a proof macro contains a "-" character, the proof script language does not support this.
            // Therefore we have to check for both versions
            // weigl, remark: it is bad style to change the call statement!
            //callStatement = callStatement.copy();
            callStatement.setCommand(callStatement.getCommand().replace("_", "-"));
            found = getBuilderImpl(callStatement, data);
        }
        if (found == null)
            throw new NoCallHandlerException(callStatement);
        return found;
    }

    @Override
    public String getHelp(CallStatement call) {
        return getBuilder(call, null).getHelp(call);
    }

    @Override
    public boolean isUninterpretedParams(CallStatement call) {
        try {
            CommandHandler cmdh = getBuilder(call, null);
            if (cmdh != null)
                return cmdh.isUninterpretedParams(call);
            return true;
        } catch (NoCallHandlerException nche) {
            return false;
        }
    }

}
