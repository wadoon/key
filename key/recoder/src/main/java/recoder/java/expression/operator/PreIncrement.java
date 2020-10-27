package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class PreIncrement extends Assignment {
    private static final long serialVersionUID = -1081530758324817367L;

    public PreIncrement() {
    }

    public PreIncrement(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    protected PreIncrement(PreIncrement proto) {
        super(proto);
        makeParentRoleValid();
    }

    public PreIncrement deepClone() {
        return new PreIncrement(this);
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

    public void accept(SourceVisitor v) {
        v.visitPreIncrement(this);
    }
}
