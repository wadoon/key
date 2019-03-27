package edu.kit.iti.formal.psdbg.interpreter.dbg;

import lombok.val;

public class StepBackCommand<T> extends DebuggerCommand<T> {
    @Override
    public void execute(DebuggerFramework<T> dbg) throws DebuggerException {
        val statePointer = dbg.getCurrentStatePointer();
        PTreeNode<T> stepBack =
                statePointer.getStepInvOver() != null
                        ? statePointer.getStepInvOver()
                        : statePointer.getStepInvInto();

        if (stepBack == null) {
            info("There is no previous state to the current one.");
        }
        dbg.setStatePointer(stepBack);
    }
}
