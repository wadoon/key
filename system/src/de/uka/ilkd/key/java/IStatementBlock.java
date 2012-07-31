package de.uka.ilkd.key.java;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.ProgramPrefix;

public interface IStatementBlock extends NonTerminalProgramElement, ProgramPrefix {

	/**
	 *      Get body.
	 *      @return the statement array wrapper.
	 */

	public abstract ImmutableArray<? extends Statement> getBody();

	/**
	 *      Get the number of statements in this container.
	 *      @return the number of statements.
	 */

	public abstract int getStatementCount();

	public abstract Statement getStatementAt(int index);

}