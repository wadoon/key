package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.keyabs.abs.expression.ABSLiteralExp;


public class ABSLiteralPattern extends ABSNonTerminalProgramElement implements IABSPattern {

	private final ABSLiteralExp literal;
	
	public ABSLiteralPattern(ABSLiteralExp literal) {
		this.literal = literal;
	}
	
	public ABSLiteralExp getLiteral() {
		return literal;
	}
	
	@Override
	public int getChildCount() {
		return 1;
	}

	@Override
	public ProgramElement getChildAt(int index) {
		return literal;
	}
	
	@Override
	public void visit(ABSVisitor v) {
		v.performActionOnABSLiteralPattern(this);
	}
}