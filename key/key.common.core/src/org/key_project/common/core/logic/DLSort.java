package org.key_project.common.core.logic;

public interface DLSort extends Named {

    /**
     * Tells whether the given sort is a reflexive, transitive subsort of this 
     * sort.
     */
    boolean extendsTrans(DLSort s);
    
    /**
     * Tells whether this sort has no exact elements.
     */
    boolean isAbstract();

}
