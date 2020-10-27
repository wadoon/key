package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class ShiftRight extends Operator {
    private static final long serialVersionUID = -3676799631907980532L;

    public ShiftRight() {
    }

    public ShiftRight(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected ShiftRight(ShiftRight proto) {
        super(proto);
        makeParentRoleValid();
    }

    public ShiftRight deepClone() {
        return new ShiftRight(this);
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
        v.visitShiftRight(this);
    }
}
