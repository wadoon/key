package recoder.java.expression;

import recoder.java.*;

public abstract class Literal extends JavaProgramElement implements Expression, TerminalProgramElement {
    protected ExpressionContainer expressionParent;

    public Literal() {
    }

    protected Literal(Literal proto) {
        super(proto);
    }

    public NonTerminalProgramElement getASTParent() {
        return this.expressionParent;
    }

    public ExpressionContainer getExpressionContainer() {
        return this.expressionParent;
    }

    public void setExpressionContainer(ExpressionContainer c) {
        this.expressionParent = c;
    }

    public abstract Object getEquivalentJavaType();
}
