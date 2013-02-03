package de.uka.ilkd.key.testgeneration.core.model;

import java.util.List;
import java.util.Map;

/**
 * A Model represents a set of variables (here represented by
 * {@link IModelObject}) on the heap, together with relevant metadata and value
 * bindings.
 * <p>
 * In the context of KeYTestGen2, the specific use of a Model is to describe a
 * heapstate which will cause the execution of a specific test case to have a
 * specific effect, such as taking a desired execution path. In particular, it
 * represents a set of values which will satisfy a path condition for a given
 * part of a symbolic execution tree.
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
    List<? extends IModelObject> getVariables(IModelFilter... filters);

    /**
     * Returns a mapping between the name of each heap variable (which must per
     * definition be unique) to its corresponding value.
     * 
     * @param filters
     *            a set of filters which each mapped variable must satisfy.
     * @return
     */
    Map<String, ? extends IModelObject> getVariableNameMapping(
            IModelFilter... filters);

    /**
     * A filter which can be used in order to select a subset
     * 
     * @author christopher
     */
    interface IModelFilter {

        boolean satisfies(IModelObject variable);
    }
}