package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementContainer;

public class ABSWhileStatement extends ABSNonTerminalProgramElement implements
	IABSStatement, ExpressionContainer, StatementContainer {

    private final IABSPureExpression condition;
    private final IABSStatement body;

    public ABSWhileStatement(IABSPureExpression condition, IABSStatement body) {
        super();
        this.condition = condition;
        this.body = body;
    }
    
    public IABSPureExpression getCondition() {
	return condition;
    }

    public IABSStatement getBody() {
	return body;
    }
    
    @Override
    public int getChildCount() {
	return 2;
    }

    @Override
    public ProgramElement getChildAt(int index) {
	if (index == 0) {
	    return condition;
	} else if (index == 1) {
	    return body;
	}
	throw new IndexOutOfBoundsException("A while statement has only two children.");
    }

    @Override
    public int getStatementCount() {
	return 1;
    }

    @Override
    public Statement getStatementAt(int index) {
	if (index != 0) {
	    throw new IndexOutOfBoundsException("A while statement contains the body as only statement." + "" +
	    		" And has no "+index+" statement.");
	}
	return body;
    }

    @Override
    public int getExpressionCount() {
	return 1;
    }

    @Override
    public Expression getExpressionAt(int index) {
	if (index != 0) {
	    throw new IndexOutOfBoundsException("A while statement contains as expression only its condition.");
	}
	return condition;
    }

    @Override
    public void visit(ABSVisitor v) {
	v.performActionOnABSWhileStatement(this);
    }

}
