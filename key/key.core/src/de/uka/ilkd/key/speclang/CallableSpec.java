package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public class CallableSpec {
    private final ImmutableList<CallableServSpec> callableServs;
    private final boolean everythingCallable;
    
    public CallableSpec(ImmutableList<CallableServSpec> callableServs) {
        this.callableServs = callableServs;
        everythingCallable = false;
    }
    
    
    public CallableSpec() {
        everythingCallable = true;
        callableServs = ImmutableSLList.<CallableServSpec>nil();
    }
    
    public boolean restrictsCalls() {
        return !everythingCallable;
    }
    
    public ImmutableList<CallableServSpec> getCallableServices() {
        if (restrictsCalls()) {
            return callableServs;
        } else {
            throw new IllegalStateException("Can't get a list of callables in a non-restrictive CallableSpec!");
        }
    }
    
    @Override 
    public String toString() {
        if (restrictsCalls()) {
            return "callable " + callableServs;
        } else {
            return "callable \\everything";
        }
            
    }
}
