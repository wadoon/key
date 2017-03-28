package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

public class LeaveCommand extends NoArgumentCommand {

    @Override
    public String getName() {
        return "leave";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl,
            Void args, EngineState state) throws ScriptException, InterruptedException {
        Goal goal = state.getFirstOpenGoal();
        System.err.println("Deactivating " + goal.node().serialNr());
        goal.setEnabled(false);
    }

}
