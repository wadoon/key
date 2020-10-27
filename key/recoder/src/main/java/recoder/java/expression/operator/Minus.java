package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class Minus extends Operator {
    private static final long serialVersionUID = 6139443256879639859L;

    public Minus() {
    }

    public Minus(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected Minus(Minus proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Minus deepClone() {
        return new Minus(this);
    }

    public int getArity() {
        return 2;
    }

    public int getPrecedence() {
        return 3;
    }

    public int getNotation() {
        return 1;
    }

    public void accept(SourceVisitor v) {
        v.visitMinus(this);
    }
}
