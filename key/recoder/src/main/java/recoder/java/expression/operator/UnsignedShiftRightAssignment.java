package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class UnsignedShiftRightAssignment extends Assignment {
    private static final long serialVersionUID = 1895345140424768114L;

    public UnsignedShiftRightAssignment() {
    }

    public UnsignedShiftRightAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected UnsignedShiftRightAssignment(UnsignedShiftRightAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    public UnsignedShiftRightAssignment deepClone() {
        return new UnsignedShiftRightAssignment(this);
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
        v.visitUnsignedShiftRightAssignment(this);
    }
}
