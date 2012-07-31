package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.IStatementBlock;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;

public interface IProgramContextAdder<S extends IStatementBlock> {

	/**
	 * wraps the context around the statements found in the putIn block   
	 */
	public abstract IStatementBlock start(
			NonTerminalProgramElement context, S putIn,
			ContextStatementBlockInstantiation ct);

}