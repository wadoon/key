package de.uka.ilkd.key.nui.model;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.nui.util.IAcceptSequentFilter;
import de.uka.ilkd.key.nui.util.IStatusManager;

public class Context {

    private ProofManager proofManager = null;

    /**
     * Lazy loaded proofManager
     * @return the current or a new proofManager
     */
    public ProofManager getProofManager() {
        if (proofManager == null){
            proofManager = new ProofManager(status);
        }
        return proofManager;
    }

    private IStatusManager status = null;

    /**
     * Returns an Object of Type IStatusManager that supports printing status texts.
     * @return
     */
    public IStatusManager getStatusManager() {
        return status;
    }
    
    /**
     * sets the StatusManager for this context. Use with caution. This doesn't update 
     * the references to the StatusManager of this context that have been set before.
     * @param value probably an UI component that supports printing a status.
     */
    public void setStatusManager(IStatusManager value){
        status = value;
    }
    
    public Context() {
    }
    
    //XXX ulgy workaround ---
    private List<IAcceptSequentFilter> acceptSequentFilters = new LinkedList<>();
    public void registerFilterConsumer(IAcceptSequentFilter acceptSequentFilter){
        acceptSequentFilters.add(acceptSequentFilter);
    }
    
    public void unregisterFilterConsumer(IAcceptSequentFilter acceptSequentFilter){
        acceptSequentFilters.remove(acceptSequentFilter);
    }
    
    public void acceptFilter(PrintFilter filter){
        for(IAcceptSequentFilter consumer: acceptSequentFilters){
            consumer.Apply(filter);
        }
    }
    // ---
}
