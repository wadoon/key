package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

public class LessThan extends ComparativeOperator {
    private static final long serialVersionUID = 4124515513475981206L;

    public LessThan() {
    }

    public LessThan(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected LessThan(LessThan proto) {
        super(proto);
        makeParentRoleValid();
    }

    public LessThan deepClone() {
        return new LessThan(this);
    }

    public int getPrecedence() {
        return 5;
    }

    public void accept(SourceVisitor v) {
        v.visitLessThan(this);
    }
}
