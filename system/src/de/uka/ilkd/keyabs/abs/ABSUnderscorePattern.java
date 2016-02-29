package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.ProgramElement;

public class ABSUnderscorePattern extends ABSNonTerminalProgramElement implements IABSPattern{
    
	@Override
	public void visit(ABSVisitor v) {
		v.performActionOnABSUnderscorePattern(this);
	}

    public String toString() {
        return "_";
    }

	@Override
	public int getChildCount() {
		return 0;
	}

	@Override
	public ProgramElement getChildAt(int index) {
		return null;
	}

}
