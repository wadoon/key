package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionConstraint;

/**
 * <p>
 * A constrained considered during symbolic execution.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionConstraint} which
 * is instantiated lazily by the {@link IExecutionNode} and
 * {@link IExecutionValue} implementations.
 * </p>
 * @author Martin Hentschel
 * @see IExecutionNode
 * @see IExecutionValue
 * @see ExecutionConstraint
 */
public interface IExecutionConstraint extends IExecutionElement {
   /**
    * Returns the {@link JavaDLTerm} representing the constraint.
    * @return The {@link JavaDLTerm} representing the constraint.
    */
   public JavaDLTerm getTerm();
}
