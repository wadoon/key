package de.uka.ilkd.key.util;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Term;

public class DependencyClusterSpec {
    

    private final ImmutableList<Lowlist> lowIn;
    private final ImmutableList<Lowlist> lowOut;
    private final ImmutableList<Term> lowState;
    private final ImmutableList<Term> newObjects;
    
    private final ImmutableList<VisibilityCondition> visible;
    
    private final String identifier;


    public DependencyClusterSpec(ImmutableList<Lowlist> lowIn, ImmutableList<Lowlist> lowOut, ImmutableList<Term> lowState, ImmutableList<VisibilityCondition> visible, ImmutableList<Term> newObjects, String identifier) {
        this.lowIn = lowIn;
        this.lowOut = lowOut;
        this.lowState = lowState;
        this.visible = visible;
        this.newObjects = newObjects;
        this.identifier = identifier;
    }


    public ImmutableList<Lowlist> getLowOut() {
        return lowOut;
    }

    public ImmutableList<Lowlist> getLowIn() {
        return lowIn;
    }

    public ImmutableList<Term> getLowState() {
        return lowState;
    }

    public ImmutableList<Term> getNewObjects() {
        return newObjects;
    }

    public ImmutableList<VisibilityCondition> getVisible() {
        return visible;
    }
    
    public String getIdentifier() {
        return identifier;
    }
    
    
    @Override
    public String toString() {
        return "LowIn: " + lowIn + "\n" +
                "LowOut: " + lowOut + "\n" +
                "lowState: " + lowState + "\n" +
                "Visible: " + visible + "\n" +
                "New Objects: " + newObjects;
    }
}
