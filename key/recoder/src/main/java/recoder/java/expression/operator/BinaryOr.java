package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class BinaryOr extends Operator {
    private static final long serialVersionUID = -7549894415250172486L;

    public BinaryOr() {
    }

    public BinaryOr(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected BinaryOr(BinaryOr proto) {
        super(proto);
        makeParentRoleValid();
    }

    public BinaryOr deepClone() {
        return new BinaryOr(this);
    }

    public int getArity() {
        return 2;
    }

    public int getPrecedence() {
        return 9;
    }

    public int getNotation() {
        return 1;
    }

    public void accept(SourceVisitor v) {
        v.visitBinaryOr(this);
    }
}
