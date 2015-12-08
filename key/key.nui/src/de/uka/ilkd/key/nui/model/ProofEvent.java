package de.uka.ilkd.key.nui.model;

import de.uka.ilkd.key.proof.Proof;

public class ProofEvent {

    private Proof proof;

    /**
     * Constructor
     */
    public ProofEvent(Proof proof) {
        this.proof = proof;
    }

    /**
     * Getter method for a proof.
     * 
     * @return The loaded Proof.
     */
    public Proof proof() {
        return this.proof;
    }
}
