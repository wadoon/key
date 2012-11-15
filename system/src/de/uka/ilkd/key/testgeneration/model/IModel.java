package de.uka.ilkd.key.testgeneration.model;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.logic.Term;

/**
 * In order to make a testcase behave in a certain way (i.e. take a certain path
 * of execution), it is necessary to start the testcase in a heapstate which
 * will cause it to behave the way we desire.
 * <p>
 * A Model represents such a partial heapstate. It is a set of value assignments for a
 * set of variables, s.t. substituting those values for the same variables in a
 * {@link Term} formula will satisfy that formula.
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