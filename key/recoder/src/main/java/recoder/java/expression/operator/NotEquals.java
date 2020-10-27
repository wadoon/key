package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

public class NotEquals extends ComparativeOperator {
    private static final long serialVersionUID = -4821815905384213846L;

    public NotEquals() {
    }

    public NotEquals(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected NotEquals(NotEquals proto) {
        super(proto);
        makeParentRoleValid();
    }

    public NotEquals deepClone() {
        return new NotEquals(this);
    }

    public int getPrecedence() {
        return 6;
    }

    public void accept(SourceVisitor v) {
        v.visitNotEquals(this);
    }
}
