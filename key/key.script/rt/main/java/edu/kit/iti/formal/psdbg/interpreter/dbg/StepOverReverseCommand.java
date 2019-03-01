package edu.kit.iti.formal.psdbg.interpreter.dbg;

import lombok.val;

public class StepOverReverseCommand<T> extends DebuggerCommand<T> {
    @Override
    public void execute(DebuggerFramework<T> dbg) throws DebuggerException {
        val statePointer = dbg.getCurrentStatePointer();
        PTreeNode<T> stepOverReverse = statePointer.getStepInvOver();
        if (stepOverReverse == null) {
            int size = statePointer.getContextNodes().size();
            dbg.setStatePointer(statePointer.getContextNodes().get(size - 1));
            /*if(statePointer.isAtomic()) {
                dbg.setStatePointer(statePointer);
            }else{
                info("There is no previous state to the current one.");

            }*/
            //state before statement
        } else {
            dbg.setStatePointer(stepOverReverse);
        }
    }
}
