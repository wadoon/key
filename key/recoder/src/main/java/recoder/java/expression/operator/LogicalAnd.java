package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class LogicalAnd extends Operator {
    private static final long serialVersionUID = -2981535131033326663L;

    public LogicalAnd() {
    }

    public LogicalAnd(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected LogicalAnd(LogicalAnd proto) {
        super(proto);
        makeParentRoleValid();
    }

    public LogicalAnd deepClone() {
        return new LogicalAnd(this);
    }

    public int getArity() {
        return 2;
    }

    public int getPrecedence() {
        return 10;
    }

    public int getNotation() {
        return 1;
    }

    public void accept(SourceVisitor v) {
        v.visitLogicalAnd(this);
    }
}
