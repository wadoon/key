package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class Divide extends Operator {
    private static final long serialVersionUID = -5919215185261848809L;

    public Divide() {
    }

    public Divide(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected Divide(Divide proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Divide deepClone() {
        return new Divide(this);
    }

    public int getArity() {
        return 2;
    }

    public int getPrecedence() {
        return 2;
    }

    public int getNotation() {
        return 1;
    }

    public void accept(SourceVisitor v) {
        v.visitDivide(this);
    }
}
