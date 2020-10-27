package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class UnsignedShiftRight extends Operator {
    private static final long serialVersionUID = 638313602392128439L;

    public UnsignedShiftRight() {
    }

    public UnsignedShiftRight(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected UnsignedShiftRight(UnsignedShiftRight proto) {
        super(proto);
        makeParentRoleValid();
    }

    public UnsignedShiftRight deepClone() {
        return new UnsignedShiftRight(this);
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
        v.visitUnsignedShiftRight(this);
    }
}
