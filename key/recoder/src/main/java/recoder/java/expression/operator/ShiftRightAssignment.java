package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class ShiftRightAssignment extends Assignment {
    private static final long serialVersionUID = 704056071320435092L;

    public ShiftRightAssignment() {
    }

    public ShiftRightAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected ShiftRightAssignment(ShiftRightAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    public ShiftRightAssignment deepClone() {
        return new ShiftRightAssignment(this);
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
        v.visitShiftRightAssignment(this);
    }
}
