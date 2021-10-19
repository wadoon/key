package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.ProofCommandStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverTaskListener;
import org.key_project.util.collection.ImmutableList;

import java.util.Map;

public class ApplyScriptsMacro extends AbstractProofMacro {
    private final Map<Goal, ProofCommandStatement> detectedCommands;

    public ApplyScriptsMacro(Map<Goal, ProofCommandStatement> detectedCommands) {
        this.detectedCommands = detectedCommands;
    }

    @Override
    public String getName() {
        return "null";
    }

    @Override
    public String getCategory() {
        return "null";
    }

    @Override
    public String getDescription() {
        return "null";
    }

    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        // if one of the goals has a command: apply
        return goals.exists(g -> detectedCommands.containsKey(g));
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener) throws InterruptedException, Exception {
        for (Goal goal : goals) {
            ProofCommandStatement cmd = detectedCommands.get(goal);
            if (cmd == null) {
                continue;
            }
            Location loc = new Location(cmd.getPositionInfo().getURI().toURL(),
                    cmd.getPositionInfo().getStartPosition().getLine(),
                    cmd.getPositionInfo().getStartPosition().getColumn());
            ProofScriptEngine pse = new ProofScriptEngine(cmd.getCommand(), loc, goal);
            pse.execute(uic, proof);
        }
        return new ProofMacroFinishedInfo(this, proof);
    }
}
