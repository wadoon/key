package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class BinaryAndAssignment extends Assignment {
    private static final long serialVersionUID = -5443127019426961308L;

    public BinaryAndAssignment() {
    }

    public BinaryAndAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected BinaryAndAssignment(BinaryAndAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    public BinaryAndAssignment deepClone() {
        return new BinaryAndAssignment(this);
    }

    public int getArity() {
        return 2;
    }

    public int getPrecedence() {
        return 13;
    }

    public int getNotation() {
        return 1;
    }

    public void accept(SourceVisitor v) {
        v.visitBinaryAndAssignment(this);
    }
}
