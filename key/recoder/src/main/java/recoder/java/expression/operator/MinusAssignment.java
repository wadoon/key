package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class MinusAssignment extends Assignment {
    private static final long serialVersionUID = -1043954220632471820L;

    public MinusAssignment() {
    }

    public MinusAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected MinusAssignment(MinusAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    public MinusAssignment deepClone() {
        return new MinusAssignment(this);
    }

    public int getArity() {
        return 2;
    }

    public int getPrecedence() {
        return 13;
    }

    public int getNotation() {
        return 1;
    }

    public void accept(SourceVisitor v) {
        v.visitMinusAssignment(this);
    }
}
