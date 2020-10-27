package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class PreDecrement extends Assignment {
    private static final long serialVersionUID = -7068320649989091567L;

    public PreDecrement() {
    }

    public PreDecrement(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    protected PreDecrement(PreDecrement proto) {
        super(proto);
        makeParentRoleValid();
    }

    public PreDecrement deepClone() {
        return new PreDecrement(this);
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
        v.visitPreDecrement(this);
    }
}
