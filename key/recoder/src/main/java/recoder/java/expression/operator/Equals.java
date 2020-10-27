package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

public class Equals extends ComparativeOperator {
    private static final long serialVersionUID = -2291841565483675639L;

    public Equals() {
    }

    public Equals(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected Equals(Equals proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Equals deepClone() {
        return new Equals(this);
    }

    public int getPrecedence() {
        return 6;
    }

    public void accept(SourceVisitor v) {
        v.visitEquals(this);
    }
}
