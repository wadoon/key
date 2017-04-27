package de.uka.ilkd.key.api;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.util.collection.ImmutableList;

import java.io.IOException;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
public class ProofApi {
    private final KeYEnvironment env;
    private final Proof proof;
    private Object firstOpenGoal;

    ProofApi(Proof proof, KeYEnvironment<?> currentEnv) {
        this.proof = proof;
        this.env = currentEnv;
    }

    public ScriptApi getScriptApi() {
        return new ScriptApi(this);
    }

    /**
     * Save current Proof-> ProofApi
     */
    public void saveProof() throws IOException {
        //TODO
    }

    KeYEnvironment getEnv() {
        return env;
    }

    Proof getProof() {
        return proof;
    }

    public List<ProjectedNode> getOpenGoals() {
        ImmutableList<Goal> goals = proof.openGoals();
        return goals.stream()
                .map(g -> new ProjectedNode(g.node(), null))
                .collect(Collectors.toList());
    }

    public ProjectedNode getFirstOpenGoal() {
        return getOpenGoals().get(0);
    }
}
