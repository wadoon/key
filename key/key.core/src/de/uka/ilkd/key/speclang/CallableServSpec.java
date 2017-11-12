package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;

public class CallableServSpec {
    private final IProgramMethod serv;
    private final Term client;
    
    public CallableServSpec(IProgramMethod serv, Term client) {
        this.serv = serv;
        this.client = client;
    }
    
    public IProgramMethod getService() {
        return serv;
    }
    
    public Term getClient() {
        return client;
    }
    
    @Override
    public String toString() {
        return "Callable Service: " + client + " . " + serv;
    }
    
}
