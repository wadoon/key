package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

public class GreaterThan extends ComparativeOperator {
    private static final long serialVersionUID = -5808604922619258847L;

    public GreaterThan() {
    }

    public GreaterThan(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected GreaterThan(GreaterThan proto) {
        super(proto);
        makeParentRoleValid();
    }

    public GreaterThan deepClone() {
        return new GreaterThan(this);
    }

    public int getPrecedence() {
        return 5;
    }

    public void accept(SourceVisitor v) {
        v.visitGreaterThan(this);
    }
}
