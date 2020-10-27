package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class Negative extends Operator {
    private static final long serialVersionUID = -7715433043154997463L;

    public Negative() {
    }

    public Negative(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    protected Negative(Negative proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Negative deepClone() {
        return new Negative(this);
    }

    public int getArity() {
        return 1;
    }

    public int getPrecedence() {
        return 1;
    }

    public int getNotation() {
        return 0;
    }

    public boolean isLeftAssociative() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitNegative(this);
    }
}
