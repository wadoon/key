package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;

public class CallableSpec {
    private final ImmutableList<CallableServSpec> callableServs;
    
    public CallableSpec(ImmutableList<CallableServSpec> callableServs) {
        this.callableServs = callableServs;
        
        //TODO JK debug output
        System.out.println("testHere: " + callableServs);
    }
}
