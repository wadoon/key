package de.uka.ilkd.key.abstractexecution.java;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractStatement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.Named;

/**
 * {@link AbstractProgramElement}s are the core of <em>Abstract Execution</em>.
 * So far, {@link AbstractStatement}s and {@link AbstractExpression}s are
 * implemented.
 *
 * @author Dominic Steinhoefel
 */
public interface AbstractProgramElement extends ProgramElement, Named {
    /**
     * @return The identifier of this {@link AbstractProgramElement}.
     */
    String getId();
}
