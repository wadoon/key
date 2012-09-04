package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.ProgramElement;

public class ABSAwaitStatement extends ABSNonTerminalProgramElement implements
	IABSStatement, ExpressionContainer {

    private final IABSPureExpression condition;
    
    public ABSAwaitStatement(IABSPureExpression condition) {
	this.condition = condition;
    }

    public IABSPureExpression getCondition() {
	return condition;
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

    @Override
    public void visit(ABSVisitor v) {
	v.performActionOnABSAwaitStatement(this);
    }

}
