package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class Positive extends Operator {
    private static final long serialVersionUID = 1940491451479434738L;

    public Positive() {
    }

    public Positive(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    protected Positive(Positive proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Positive deepClone() {
        return new Positive(this);
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
        v.visitPositive(this);
    }
}
