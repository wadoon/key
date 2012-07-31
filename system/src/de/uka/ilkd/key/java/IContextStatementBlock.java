package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.reference.IExecutionContext;

public interface IContextStatementBlock {

	public abstract boolean requiresExplicitExecutionContextMatch();

	public abstract IExecutionContext getExecutionContext();

}