package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class PlusAssignment extends Assignment {
    private static final long serialVersionUID = 316506987506404732L;

    public PlusAssignment() {
    }

    public PlusAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected PlusAssignment(PlusAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    public PlusAssignment deepClone() {
        return new PlusAssignment(this);
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
        v.visitPlusAssignment(this);
    }
}
