package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class PostDecrement extends Assignment {
    private static final long serialVersionUID = -1562954246447453685L;

    public PostDecrement() {
    }

    public PostDecrement(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    protected PostDecrement(PostDecrement proto) {
        super(proto);
        makeParentRoleValid();
    }

    public PostDecrement deepClone() {
        return new PostDecrement(this);
    }

    public int getArity() {
        return 1;
    }

    public int getPrecedence() {
        return 1;
    }

    public int getNotation() {
        return 2;
    }

    public void accept(SourceVisitor v) {
        v.visitPostDecrement(this);
    }
}
