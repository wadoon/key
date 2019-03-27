package edu.kit.iti.formal.psdbg.interpreter.dbg;

public abstract class DebuggerCommand<T> {
    public abstract void execute(DebuggerFramework<T> dbg) throws DebuggerException;

    public void error(String msg) throws DebuggerException {
        throw new DebuggerException(msg, true);
    }

    public void info(String msg) throws DebuggerException {
        throw new DebuggerException(msg, false);
    }
}
