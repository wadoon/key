package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class DivideAssignment extends Assignment {
    private static final long serialVersionUID = 3806208146891527861L;

    public DivideAssignment() {
    }

    public DivideAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected DivideAssignment(DivideAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    public DivideAssignment deepClone() {
        return new DivideAssignment(this);
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
        v.visitDivideAssignment(this);
    }
}
