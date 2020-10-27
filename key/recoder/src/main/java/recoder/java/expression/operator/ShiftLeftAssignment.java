package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class ShiftLeftAssignment extends Assignment {
    private static final long serialVersionUID = 2965087191992910283L;

    public ShiftLeftAssignment() {
    }

    public ShiftLeftAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected ShiftLeftAssignment(ShiftLeftAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    public ShiftLeftAssignment deepClone() {
        return new ShiftLeftAssignment(this);
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
        v.visitShiftLeftAssignment(this);
    }
}
