package recoder.java.statement;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

public class Throw extends ExpressionJumpStatement {
    private static final long serialVersionUID = -259489032726058910L;

    public Throw() {
    }

    public Throw(Expression expr) {
        super(expr);
        if (expr == null)
            throw new IllegalArgumentException("Throw requires one argument");
        makeParentRoleValid();
    }

    protected Throw(Throw proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Throw deepClone() {
        return new Throw(this);
    }

    public void accept(SourceVisitor v) {
        v.visitThrow(this);
    }
}
