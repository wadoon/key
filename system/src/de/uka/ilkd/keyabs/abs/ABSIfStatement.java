package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.ProgramElement;

public class ABSIfStatement extends ABSNonTerminalProgramElement implements
        IABSStatement, ExpressionContainer {

    public ABSIfStatement(IABSPureExpression condition,
            IABSStatement thenBranch, IABSStatement elseBranch) {
        super();
        this.condition = condition;
        this.thenBranch = thenBranch;
        this.elseBranch = elseBranch;
    }

    private final IABSPureExpression condition;
    private final IABSStatement thenBranch;
    private final IABSStatement elseBranch;

    @Override
    public int getChildCount() {
        return elseBranch == null ? 2 : 3;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        switch (index) {
        case 0:
            return condition;
        case 1:
            return thenBranch;
        case 2:
            if (elseBranch != null) {
                return elseBranch;
            }
        }
        throw new IndexOutOfBoundsException();
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSIfStatement(this);
    }

    @Override
    public int getExpressionCount() {
        return 1;
    }

    @Override
    public Expression getExpressionAt(int index) {
        if (index == 0) {
            return condition;
        }
        throw new IndexOutOfBoundsException();
    }
    
    
    @Override
    public String toString() {
        return "if" + "(" + condition + ") { " + thenBranch + " }\n" + "else {" + elseBranch + "}"; 
    }

    public IABSPureExpression getCondition() {
        return condition;
    }
    
    public IABSStatement getThenBranch() {
        return thenBranch;
    }
    public IABSStatement getElseBranch() {
        return elseBranch;
    }

}
