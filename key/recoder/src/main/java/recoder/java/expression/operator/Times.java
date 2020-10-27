package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class Times extends Operator {
    private static final long serialVersionUID = 452019546318592957L;

    public Times() {
    }

    public Times(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected Times(Times proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Times deepClone() {
        return new Times(this);
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
        v.visitTimes(this);
    }
}
