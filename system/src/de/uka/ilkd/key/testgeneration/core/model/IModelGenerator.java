package de.uka.ilkd.key.testgeneration.core.model;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Objects implementing this interface are used in order to create
 * {@link IModel} instances for the path condition of a given
 * {@link IExecutionNode}, i.e. find a set of concrete value assignments that
 * satisfy this particular path condition.
 * 
 * @author christopher
 */
public interface IModelGenerator {

    public IModel generateModel(IExecutionNode node)
            throws ModelGeneratorException;
}
