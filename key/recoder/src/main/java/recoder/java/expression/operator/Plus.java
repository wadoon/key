package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class Plus extends Operator {
    private static final long serialVersionUID = 560126060000682104L;

    public Plus() {
    }

    public Plus(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected Plus(Plus proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Plus deepClone() {
        return new Plus(this);
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
        v.visitPlus(this);
    }
}
