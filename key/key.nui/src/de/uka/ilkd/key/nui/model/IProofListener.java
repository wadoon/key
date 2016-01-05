package de.uka.ilkd.key.nui.model;

import java.util.EventListener;

public interface IProofListener extends EventListener {
    public void proofUpdated(ProofEvent proofEvent);
}