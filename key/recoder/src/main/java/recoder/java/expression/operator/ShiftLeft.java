package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class ShiftLeft extends Operator {
    private static final long serialVersionUID = 840153660638293507L;

    public ShiftLeft() {
    }

    public ShiftLeft(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected ShiftLeft(ShiftLeft proto) {
        super(proto);
        makeParentRoleValid();
    }

    public ShiftLeft deepClone() {
        return new ShiftLeft(this);
    }

    public int getArity() {
        return 2;
    }

    public int getPrecedence() {
        return 4;
    }

    public int getNotation() {
        return 1;
    }

    public void accept(SourceVisitor v) {
        v.visitShiftLeft(this);
    }
}
