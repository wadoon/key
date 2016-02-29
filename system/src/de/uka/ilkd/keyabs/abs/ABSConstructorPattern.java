package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.ProgramElement;


public class ABSConstructorPattern extends ABSNonTerminalProgramElement implements IABSPattern {

	private final ABSDataConstructor literal;
	
	public ABSConstructorPattern(ABSDataConstructor literal) {
		this.literal = literal;
	}
	
	public ABSDataConstructor getLiteral() {
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
		v.performActionOnABSConstructorPattern(this);
	}

}
