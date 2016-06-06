package de.uka.ilkd.key.java.abstraction;

import org.key_project.common.core.logic.sort.Sort;


/**
 * represents a mapping from a program type to the logic sort used to represent the type
 * @author Richard Bubel
 *
 * @param <T> the program type
 */
public interface PorgramType2SortEntry<T> {

    /**
     * returns the program type 
     * @return the program type
     */
    T getProgramType();

    /**
     * returns the sort the program type is mapped to
     * @return the sort 
     */
    Sort getSort();

}