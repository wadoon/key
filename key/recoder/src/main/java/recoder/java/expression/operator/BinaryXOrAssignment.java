package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class BinaryXOrAssignment extends Assignment {
    private static final long serialVersionUID = 2881071324012163593L;

    public BinaryXOrAssignment() {
    }

    public BinaryXOrAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected BinaryXOrAssignment(BinaryXOrAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    public BinaryXOrAssignment deepClone() {
        return new BinaryXOrAssignment(this);
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
        v.visitBinaryXOrAssignment(this);
    }
}
