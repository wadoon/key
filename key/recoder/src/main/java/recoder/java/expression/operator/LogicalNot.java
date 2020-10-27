package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class LogicalNot extends Operator {
    private static final long serialVersionUID = -5172121858912066403L;

    public LogicalNot() {
    }

    public LogicalNot(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    protected LogicalNot(LogicalNot proto) {
        super(proto);
        makeParentRoleValid();
    }

    public LogicalNot deepClone() {
        return new LogicalNot(this);
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
        v.visitLogicalNot(this);
    }
}
