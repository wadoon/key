package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

public class LessOrEquals extends ComparativeOperator {
    private static final long serialVersionUID = 2156040099278098771L;

    public LessOrEquals() {
    }

    public LessOrEquals(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected LessOrEquals(LessOrEquals proto) {
        super(proto);
        makeParentRoleValid();
    }

    public LessOrEquals deepClone() {
        return new LessOrEquals(this);
    }

    public int getPrecedence() {
        return 5;
    }

    public void accept(SourceVisitor v) {
        v.visitLessOrEquals(this);
    }
}
