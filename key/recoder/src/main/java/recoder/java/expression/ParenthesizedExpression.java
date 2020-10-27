package recoder.java.expression;

import recoder.java.*;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;

public class ParenthesizedExpression extends Operator implements ExpressionStatement, ReferencePrefix {
    private static final long serialVersionUID = 5087638517523549125L;

    protected ReferenceSuffix accessParent;

    protected StatementContainer statementParent;

    public ParenthesizedExpression() {
    }

    public ParenthesizedExpression(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    protected ParenthesizedExpression(ParenthesizedExpression proto) {
        super(proto);
        makeParentRoleValid();
    }

    public ParenthesizedExpression deepClone() {
        return new ParenthesizedExpression(this);
    }

    public NonTerminalProgramElement getASTParent() {
        if (this.expressionParent != null)
            return this.expressionParent;
        if (this.accessParent != null)
            return this.accessParent;
        return this.statementParent;
    }

    public StatementContainer getStatementContainer() {
        return this.statementParent;
    }

    public void setStatementContainer(StatementContainer parent) {
        this.statementParent = parent;
        this.expressionParent = null;
        this.accessParent = null;
    }

    public void setExpressionContainer(ExpressionContainer c) {
        this.expressionParent = c;
        this.statementParent = null;
        this.accessParent = null;
    }

    public int getChildCount() {
        return (this.children != null) ? this.children.size() : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (this.children != null)
            return this.children.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public ReferenceSuffix getReferenceSuffix() {
        return this.accessParent;
    }

    public void setReferenceSuffix(ReferenceSuffix path) {
        this.accessParent = path;
        this.expressionParent = null;
        this.statementParent = null;
    }

    public int getArity() {
        return 1;
    }

    public int getPrecedence() {
        return 0;
    }

    public int getNotation() {
        return 1;
    }

    public SourceElement getFirstElement() {
        return this;
    }

    public SourceElement getLastElement() {
        return this;
    }

    public void accept(SourceVisitor v) {
        v.visitParenthesizedExpression(this);
    }
}
