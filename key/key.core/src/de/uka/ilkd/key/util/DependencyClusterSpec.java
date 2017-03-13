package de.uka.ilkd.key.util;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Term;

public class DependencyClusterSpec {
    public static final DependencyClusterSpec EMPTY_DEP_CLUSTER_SPEC = new DependencyClusterSpec();
    
    //TODO JK build class
    private final ImmutableList<Lowlist> lowIn;
    private final ImmutableList<Lowlist> lowOut;
    private final ImmutableList<Term> lowState;
    private final ImmutableList<Term> newObjects;
    
    private final ImmutableList<VisibilityCondition> visible; //TODO JK simple terms wont do it I suspect...


    public DependencyClusterSpec(ImmutableList<Lowlist> lowIn, ImmutableList<Lowlist> lowOut, ImmutableList<Term> lowState, ImmutableList<VisibilityCondition> visible) {
        this(lowIn, lowOut,lowState, visible, null);
    }
    
    public DependencyClusterSpec(ImmutableList<Lowlist> lowIn, ImmutableList<Lowlist> lowOut, ImmutableList<Term> lowState, ImmutableList<VisibilityCondition> visible, ImmutableList<Term> newObjects) {
        this.lowIn = lowIn;
        this.lowOut = lowOut;
        this.lowState = lowState;
        this.visible = visible;
        this.newObjects = newObjects;
    }
    
    private DependencyClusterSpec() {
        this.lowIn = ImmutableSLList.<Lowlist>nil();
        this.lowOut = ImmutableSLList.<Lowlist>nil();
        this.lowState = ImmutableSLList.<Term>nil();
        this.visible = ImmutableSLList.<VisibilityCondition>nil();
        this.newObjects = ImmutableSLList.<Term>nil();
    }
}
