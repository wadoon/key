package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.util.Lowlist;
import de.uka.ilkd.key.util.VisibilityCondition;

public class ServiceDependencyClusterSpec implements DependencyClusterSpec {
    

    private final ImmutableList<Lowlist> lowIn;
    private final ImmutableList<Lowlist> lowOut;
    private final ImmutableList<Term> lowState;
    private final ImmutableList<Term> newObjects;
    
    private final ImmutableList<VisibilityCondition> visible;
    
    private final String label;


    public ServiceDependencyClusterSpec(ImmutableList<Lowlist> lowIn, ImmutableList<Lowlist> lowOut, ImmutableList<Term> lowState, ImmutableList<VisibilityCondition> visible, ImmutableList<Term> newObjects, String label) {
        this.lowIn = lowIn;
        this.lowOut = lowOut;
        this.lowState = lowState;
        this.visible = visible;
        this.newObjects = newObjects;
        this.label = label;
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
    
    public String getLabel() {
        return label;
    }
    
    
    @Override
    public String toString() {
        return  "Label: " + label+ "\n" +
                "LowIn: " + lowIn + "\n" +
                "LowOut: " + lowOut + "\n" +
                "lowState: " + lowState + "\n" +
                "Visible: " + visible + "\n" +
                "New Objects: " + newObjects;
    }


    @Override
    public Function getEquivEventPredicate() {
        return null;
        // TODO Auto-generated method stub

    }


    @Override
    public Function getAgreePrePredicate() {
        return null;
        // TODO Auto-generated method stub

    }


    @Override
    public Function getVisibilityPredicate() {
        return null;
        // TODO Auto-generated method stub

    }


    @Override
    public RewriteTaclet getEquivEventDefinition() {
        return null;
        // TODO Auto-generated method stub

    }


    @Override
    public RewriteTaclet getAgreePreDefinition() {
        return null;
        // TODO Auto-generated method stub

    }


    @Override
    public RewriteTaclet getVisibilityDefinition() {
        return null;
        // TODO Auto-generated method stub

    }
}
