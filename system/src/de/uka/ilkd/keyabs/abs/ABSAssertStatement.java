package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.ProgramElement;

public class ABSAssertStatement extends ABSNonTerminalProgramElement implements
	IABSStatement, ExpressionContainer {
	
	private final IABSPureExpression condition;
	
	public ABSAssertStatement(IABSPureExpression condition) {
		this.condition = condition;
	}


	@Override
	public int getChildCount() {
		return 1;
	}

	@Override
	public ProgramElement getChildAt(int index) {
		return condition;
	}

	@Override
	public int getExpressionCount() {
		return 1;
	}

	@Override
	public Expression getExpressionAt(int index) {
		return condition;
	}

	public IABSPureExpression getCondition() {
		return condition;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
	    sb.append("assert ");
	    sb.append(condition).append(" \n");
	    return sb.toString();
	}

	@Override
	public void visit(ABSVisitor v) {
		v.performActionOnABSAssertStatement(this);
	}
}
