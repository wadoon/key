package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class LogicalOr extends Operator {
    private static final long serialVersionUID = 2782994601085095817L;

    public LogicalOr() {
    }

    public LogicalOr(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected LogicalOr(LogicalOr proto) {
        super(proto);
        makeParentRoleValid();
    }

    public LogicalOr deepClone() {
        return new LogicalOr(this);
    }

    public int getArity() {
        return 2;
    }

    public int getPrecedence() {
        return 11;
    }

    public int getNotation() {
        return 1;
    }

    public void accept(SourceVisitor v) {
        v.visitLogicalOr(this);
    }
}
