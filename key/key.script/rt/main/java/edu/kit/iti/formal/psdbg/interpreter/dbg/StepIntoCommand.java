package edu.kit.iti.formal.psdbg.interpreter.dbg;

public class StepIntoCommand<T> extends DebuggerCommand<T> {
    @Override
    public void execute(DebuggerFramework<T> dbg) {
        PTreeNode<T> statePointer = dbg.getStatePointer();
        assert statePointer != null;
        if (statePointer.isAtomic()) { // atomic same as step over
            new StepOverCommand<T>().execute(dbg);
        } else {
            if (statePointer.getStepInto() != null) { // if there is already an step into take it!
                dbg.setStatePointer(statePointer.getStepInto());
            } else {
                if (!statePointer.isLastNode()) { // execute non last commands, one step wide!
                    dbg.releaseUntil(new Blocker.CounterBlocker(1));
                }
            }
        }
    }
}
