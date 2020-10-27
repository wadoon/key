package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class CopyAssignment extends Assignment {
    private static final long serialVersionUID = -7829333990720251044L;

    public CopyAssignment() {
    }

    public CopyAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected CopyAssignment(CopyAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    public CopyAssignment deepClone() {
        return new CopyAssignment(this);
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
        v.visitCopyAssignment(this);
    }
}
