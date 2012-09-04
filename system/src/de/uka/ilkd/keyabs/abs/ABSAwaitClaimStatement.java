package de.uka.ilkd.keyabs.abs;

public class ABSAwaitClaimStatement extends ABSAwaitStatement {

    public ABSAwaitClaimStatement(IABSPureExpression condition) {
	super(condition);
    }

    
    @Override
    public void visit(ABSVisitor v) {
	v.performActionOnABSAwaitClaimStatement(this);
    }

}
