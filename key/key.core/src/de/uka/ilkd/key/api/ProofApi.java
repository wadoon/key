package de.uka.ilkd.key.api;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;

import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
public class ProofApi {
    private final KeYEnvironment env;
    private final Proof proof;

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
}
