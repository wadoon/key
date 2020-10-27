package recoder.java.statement;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

public class Return extends ExpressionJumpStatement {
    private static final long serialVersionUID = 1L;

    public Return() {
    }

    public Return(Expression expr) {
        super(expr);
        makeParentRoleValid();
    }

    protected Return(Return proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Return deepClone() {
        return new Return(this);
    }

    public void accept(SourceVisitor v) {
        v.visitReturn(this);
    }
}
