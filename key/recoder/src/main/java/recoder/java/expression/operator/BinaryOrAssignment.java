package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class BinaryOrAssignment extends Assignment {
    private static final long serialVersionUID = 8200577893328544765L;

    public BinaryOrAssignment() {
    }

    public BinaryOrAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected BinaryOrAssignment(BinaryOrAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    public BinaryOrAssignment deepClone() {
        return new BinaryOrAssignment(this);
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
        v.visitBinaryOrAssignment(this);
    }
}
