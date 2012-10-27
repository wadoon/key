package de.uka.ilkd.key.testgeneration.model.modelgeneration;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.model.IModel;

/**
 * Objects implementing this interface are used in order to create a model for
 * the path condition of a given {@link IExecutionNode}, i.e. find a set of
 * concrete variable assignments that satisfy this particular model. The
 * representation of such a model is indicated by generic type T. Implementing
 * classes are not intended to be generic in themselves.
 * 
 * @author christopher
 */
public interface IModelGenerator {

    public IModel generateModel(IExecutionNode node)
            throws ModelGeneratorException;
}
