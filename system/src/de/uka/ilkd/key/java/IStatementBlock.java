package de.uka.ilkd.key.java;

import de.uka.ilkd.key.collection.ImmutableArray;

public interface IStatementBlock extends NonTerminalProgramElement {

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