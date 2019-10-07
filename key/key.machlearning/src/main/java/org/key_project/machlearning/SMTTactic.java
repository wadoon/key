package org.key_project.machlearning;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.ui.ConsoleUserInterfaceControl;
import org.json.simple.JSONObject;

public class SMTTactic implements Tactic {
    @Override
    public void apply(ConsoleUserInterfaceControl ui, Proof proof, Goal goal, JSONObject command) throws Exception {
        throw new UnsupportedOperationException("eventually implemented ...");
    }
}
