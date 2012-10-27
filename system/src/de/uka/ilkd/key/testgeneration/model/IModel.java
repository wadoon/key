package de.uka.ilkd.key.testgeneration.model;

import java.util.Collection;
import java.util.List;

/**
 * Represents a model of a partial heapstate during program execution. The Model
 * holds a selection of variables on the heap, together with their metadata and
 * bound values. The interface is generic to allow for multiple model
 * representations.
 * 
 * @author christopher
 */
public interface IModel<T> {

    /**
     * Get a filtered subset of variables represented in this model
     * 
     * @return
     */
    List<T> getVariables(IModelFilter<T>... filters);

    interface IModelFilter<T> {

        boolean satisfies(T object);
    }
}