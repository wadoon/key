package de.uka.ilkd.key.testgeneration.model;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.testgeneration.defaultimplementation.IModelVariable;

/**
 * Represents a model of a partial heapstate during program execution. The Model
 * holds a selection of variables on the heap, together with their metadata and
 * bound values. The interface is generic to allow for multiple model
 * representations.
 * 
 * @author christopher
 */
public interface IModel {

    /**
     * Get a subset of variables in this model. If supplied, the resultant set
     * will correspond to all sets satisfying a set of filters.
     * 
     * @param filters
     *            a set of filters which each variable in he list must satisfy.
     * @return
     */
    List<IModelVariable> getVariables(IModelFilter... filters);

    /**
     * Returns a mapping between the name of each heap variable (which must per
     * definition be unique) to its corresponding value.
     * 
     * @param filters
     *            a set of filters which each mapped variable must satisfy.
     * @return
     */
    Map<String, IModelVariable> getVariableNameMapping(IModelFilter... filters);

    /**
     * A filter which can be
     * 
     * @author christopher
     */
    interface IModelFilter {

        boolean satisfies(IModelVariable variable);
    }
}