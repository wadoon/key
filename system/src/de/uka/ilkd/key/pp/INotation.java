package de.uka.ilkd.key.pp;

import java.io.IOException;

import de.uka.ilkd.key.logic.Term;

public interface INotation {

	/** get the priority of the term */
	public abstract int getPriority();

	/**
	 * Print a term to a {@link LogicPrinter}. Concrete subclasses override
	 * this to call one of the <code>printXYZTerm</code> of
	 * {@link LogicPrinter}, which do the layout.
	 */
	public abstract void print(Term t, ILogicPrinter sp) throws IOException;

	/**
	 * Print a term without beginning a new block. See
	 * {@link LogicPrinter#printTermContinuingBlock(Term)}for the idea
	 * behind this. The standard implementation just delegates to
	 * {@link #print(Term,ILogicPrinter)}
	 */
	public abstract void printContinuingBlock(Term t, ILogicPrinter sp)
			throws IOException;

}