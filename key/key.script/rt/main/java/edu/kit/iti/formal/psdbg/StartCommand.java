package edu.kit.iti.formal.psdbg;

import edu.kit.iti.formal.psdbg.interpreter.dbg.Blocker;
import edu.kit.iti.formal.psdbg.interpreter.dbg.DebuggerCommand;
import edu.kit.iti.formal.psdbg.interpreter.dbg.DebuggerException;
import edu.kit.iti.formal.psdbg.interpreter.dbg.DebuggerFramework;
import lombok.AllArgsConstructor;
import lombok.*;

@AllArgsConstructor
public class StartCommand<T> extends DebuggerCommand<T> {
    @Getter @Setter
    private boolean directStop = true;

    @Override
    public void execute(DebuggerFramework<T> dbg) throws DebuggerException {
        dbg.releaseUntil(new Blocker.CounterBlocker(1));
        dbg.start();
    }
}
