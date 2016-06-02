package org.key_project.common.core.logic;

import org.key_project.common.core.logic.op.SortDependingFunction;
import org.key_project.util.collection.ImmutableSet;

public interface Sort extends Named {

    /**
     * Tells whether the given sort is a reflexive, transitive subsort of this 
     * sort.
     * @param services TODO
     */
    boolean extendsTrans(Sort s, TermServices<?, ?> services);
    
    /**
     * Tells whether this sort has no exact elements.
     */
    boolean isAbstract();
    
    /**
     * Returns the direct supersorts of this sort.
     */
    ImmutableSet<Sort> extendsSorts(TermServices<?,?> services);     
    
    
    /**
     * returns the cast symbol of this Sort
     */
    SortDependingFunction getCastSymbol(TermServices<?,?> services);
    
    /**
     * returns the instanceof symbol of this Sort
     */
    SortDependingFunction getInstanceofSymbol(TermServices<?,?> services);
    
    /**
     * returns the exactinstanceof symbol of this Sort
     */
    SortDependingFunction getExactInstanceofSymbol(TermServices<?,?> services);
    
    /**
     * 
     * @return
     */
    String declarationString();
    
    public final Name CAST_NAME = new Name("cast");
    final Name INSTANCE_NAME = new Name("instance");
    final Name EXACT_INSTANCE_NAME = new Name("exactInstance");    
}
