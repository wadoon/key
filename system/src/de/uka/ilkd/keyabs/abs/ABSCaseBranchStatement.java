package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.ProgramElement;

public class ABSCaseBranchStatement extends ABSNonTerminalProgramElement implements IABSCaseBranchStatement{
	
	public ABSCaseBranchStatement(IABSPattern pattern, IABSStatement statement){
		this.pattern = pattern;
		this.statement = statement;
	}

	private final IABSPattern pattern;
	private final IABSStatement statement;
	
	@Override
	public int getChildCount() {
		return 2;
	}

	public IABSPattern getPattern() {
		return pattern;
	}
	
	public IABSStatement getStatement() {
		return statement;
	}
	
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(pattern).append(" => { \n");
        sb.append(statement).append(" \n");;
        sb.append("}");
        return sb.toString();
    }
    
	@Override
	public ProgramElement getChildAt(int index) {
		if(index == 0) return pattern;
		
		return statement;
	}

	@Override
	public void visit(ABSVisitor v) {
		v.performActionOnABSCaseBranchStatement(this);
	}

}
