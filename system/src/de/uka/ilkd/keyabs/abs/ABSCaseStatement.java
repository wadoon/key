package de.uka.ilkd.keyabs.abs;

import java.util.List;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;

public class ABSCaseStatement extends ABSNonTerminalProgramElement implements IABSPureExpression, IABSCaseBranchStatement{

    public ABSCaseStatement(IABSPureExpression caseExpression, List<IABSCaseBranchStatement> branchList) {
    	this.caseExpression = caseExpression;
    	this.branches = branchList.toArray(new IABSCaseBranchStatement[branchList.size()]);
    }
  
    public ABSCaseStatement(IABSPureExpression caseExpression, IABSCaseBranchStatement[] p_branches) {
    	this.caseExpression = caseExpression;
    	this.branches = new IABSCaseBranchStatement[p_branches.length];
    	System.arraycopy(p_branches, 0, this.branches, 0, p_branches.length);
 	}

	private final IABSPureExpression caseExpression;
    private final IABSCaseBranchStatement[] branches;
    
    @Override
    public int getChildCount() {
        return 1 + branches.length;
    }
    
    @Override
    public ProgramElement getChildAt(int index) {
    	if (index == 0) return caseExpression;
    	
    	return branches[index - 1];
    }
    
    public IABSPureExpression getCaseExpression() {
        return caseExpression;
    }
  
    public int getBranchCount() {
    	return branches.length;
    }
    
    public IABSCaseBranchStatement getBranchAt(int i) {
        return branches[i];
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("case ").append(caseExpression).append(" { \n");

        for (IABSCaseBranchStatement branch : branches) {
            sb.append(branch).append('\n');
        }

        sb.append("}");
        return sb.toString();
    }
    
	@Override
	public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
		return null;
	}

	@Override
	public void visit(ABSVisitor v) {
		v.performActionOnABSCaseStatement(this);
	}
}
