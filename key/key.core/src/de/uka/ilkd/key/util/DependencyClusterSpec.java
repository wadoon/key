package de.uka.ilkd.key.util;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Term;

public class DependencyClusterSpec {
    public static final DependencyClusterSpec EMPTY_DEP_CLUSTER_SPEC = new DependencyClusterSpec();
    
    //TODO JK build class
    private final ImmutableList<Term> lowIn;
    private final ImmutableList<Term> lowOut;
    private final ImmutableList<Term> lowState;
    private final ImmutableList<Term> newObjects;
    
    private final ImmutableList<Term> visible; //TODO JK simple terms wont do it I suspect...


    public DependencyClusterSpec(ImmutableList<Term> lowIn, ImmutableList<Term> lowOut, ImmutableList<Term> lowState, ImmutableList<Term> visible) {
        this(lowIn, lowOut,lowState, visible, null);
    }
    
    public DependencyClusterSpec(ImmutableList<Term> lowIn, ImmutableList<Term> lowOut, ImmutableList<Term> lowState, ImmutableList<Term> visible, ImmutableList<Term> newObjects) {
        this.lowIn = lowIn;
        this.lowOut = lowOut;
        this.lowState = lowState;
        this.visible = visible;
        this.newObjects = newObjects;
    }
    
    private DependencyClusterSpec() {
        this.lowIn = ImmutableSLList.<Term>nil();
        this.lowOut = ImmutableSLList.<Term>nil();
        this.lowState = ImmutableSLList.<Term>nil();
        this.visible = ImmutableSLList.<Term>nil();
        this.newObjects = ImmutableSLList.<Term>nil();
    }
}
