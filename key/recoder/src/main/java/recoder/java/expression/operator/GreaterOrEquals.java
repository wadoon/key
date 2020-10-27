package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

public class GreaterOrEquals extends ComparativeOperator {
    private static final long serialVersionUID = 7710158660690500126L;

    public GreaterOrEquals() {
    }

    public GreaterOrEquals(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected GreaterOrEquals(GreaterOrEquals proto) {
        super(proto);
        makeParentRoleValid();
    }

    public GreaterOrEquals deepClone() {
        return new GreaterOrEquals(this);
    }

    public int getPrecedence() {
        return 5;
    }

    public void accept(SourceVisitor v) {
        v.visitGreaterOrEquals(this);
    }
}
