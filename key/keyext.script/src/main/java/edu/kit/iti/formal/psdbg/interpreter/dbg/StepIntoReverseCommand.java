package edu.kit.iti.formal.psdbg.interpreter.dbg;

public class StepIntoReverseCommand<T> extends DebuggerCommand<T> {

    @Override
    public void execute(DebuggerFramework<T> dbg) throws DebuggerException {
        PTreeNode<T> statePointer = dbg.getStatePointer();
        assert statePointer != null;

        if (statePointer.getStepInvInto() != null) {
            dbg.setStatePointer(statePointer.getStepInvInto());
        } else {
            if (statePointer.getStepInvOver() != null) {
                PTreeNode<T> statementBefore = statePointer.getStepInvOver();
                dbg.setStatePointer(statementBefore);
            } else{
                dbg.setStatePointer(statePointer);

                /*if (statePointer.isLastNode() || statePointer.isFirstNode()) {
                    System.out.println("We need Sonderbehandlung here");
                }*/
            }
        }
    }
}
