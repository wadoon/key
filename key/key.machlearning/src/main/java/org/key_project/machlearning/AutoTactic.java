package org.key_project.machlearning;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.prover.GoalChooser;
import de.uka.ilkd.key.prover.GoalChooserBuilder;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.ui.ConsoleUserInterfaceControl;
import org.json.simple.JSONObject;

public class AutoTactic implements Tactic {

    @Override
    public void apply(ConsoleUserInterfaceControl ui, Proof proof, Goal goal, JSONObject command) throws Exception {
        Profile profile = proof.getInitConfig().getProfile();
        GoalChooser chooser = profile.getSelectedGoalChooserBuilder().create();
        ProverCore prover = new ApplyStrategy(chooser);
        prover.start(proof, goal);
    }
}
