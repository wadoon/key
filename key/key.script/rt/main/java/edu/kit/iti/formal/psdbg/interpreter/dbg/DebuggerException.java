package edu.kit.iti.formal.psdbg.interpreter.dbg;

import lombok.Getter;

public class DebuggerException extends Exception {
    @Getter private final boolean severe;

    public DebuggerException(String msg, boolean severe) {
        super(msg);
        this.severe=severe;
    }
}
