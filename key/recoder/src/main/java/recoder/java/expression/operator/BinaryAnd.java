package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class BinaryAnd extends Operator {
    private static final long serialVersionUID = 5167112677525923924L;

    public BinaryAnd() {
    }

    public BinaryAnd(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected BinaryAnd(BinaryAnd proto) {
        super(proto);
        makeParentRoleValid();
    }

    public BinaryAnd deepClone() {
        return new BinaryAnd(this);
    }

    public final int getArity() {
        return 2;
    }

    public final int getPrecedence() {
        return 7;
    }

    public final int getNotation() {
        return 1;
    }

    public void accept(SourceVisitor v) {
        v.visitBinaryAnd(this);
    }
}
