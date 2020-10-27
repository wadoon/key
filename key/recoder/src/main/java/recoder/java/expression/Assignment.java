package recoder.java.expression;

import recoder.java.Expression;
import recoder.java.NonTerminalProgramElement;
import recoder.java.StatementContainer;

public abstract class Assignment extends Operator implements ExpressionStatement {
    protected StatementContainer statementParent;

    public Assignment() {
    }

    public Assignment(Expression unaryChild) {
        super(unaryChild);
    }

    public Assignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    protected Assignment(Assignment proto) {
        super(proto);
    }

    public NonTerminalProgramElement getASTParent() {
        if (this.expressionParent != null)
            return this.expressionParent;
        return this.statementParent;
    }

    public StatementContainer getStatementContainer() {
        return this.statementParent;
    }

    public void setStatementContainer(StatementContainer c) {
        this.statementParent = c;
    }

    public boolean isLeftAssociative() {
        return false;
    }

    public abstract Assignment deepClone();
}
