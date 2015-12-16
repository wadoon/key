package de.uka.ilkd.key.nui;

import de.uka.ilkd.key.nui.model.ProofManager;
import de.uka.ilkd.key.nui.util.IStatusManager;

public class Context {

    private ProofManager proofManager = null;

    public ProofManager getProofManager() {
        if (proofManager == null)
            proofManager = new ProofManager();
        return proofManager;
    }

    private IStatusManager status = null;

    public IStatusManager getStatusManager() {
        return status;
    }
    
    public void setStatusManager(IStatusManager value){
        status = value;
    }

    public Context() {
    }

}
