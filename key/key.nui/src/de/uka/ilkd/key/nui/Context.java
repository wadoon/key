package de.uka.ilkd.key.nui;

import de.uka.ilkd.key.nui.model.ProofManager;

public class Context {

    private ProofManager proofManager = null;
    
    public ProofManager getProofManager(){
        if(proofManager == null)
            proofManager = new ProofManager();
        return proofManager;
    }
    
    public Context() {
    }

}
