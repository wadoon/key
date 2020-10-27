package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class BinaryXOr extends Operator {
    private static final long serialVersionUID = -7163139482513251225L;

    public BinaryXOr() {
    }

    public BinaryXOr(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected BinaryXOr(BinaryXOr proto) {
        super(proto);
        makeParentRoleValid();
    }

    public BinaryXOr deepClone() {
        return new BinaryXOr(this);
    }

    public int getArity() {
        return 2;
    }

    public int getPrecedence() {
        return 8;
    }

    public int getNotation() {
        return 1;
    }

    public void accept(SourceVisitor v) {
        v.visitBinaryXOr(this);
    }
}
