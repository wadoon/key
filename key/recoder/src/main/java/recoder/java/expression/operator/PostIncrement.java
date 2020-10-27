package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class PostIncrement extends Assignment {
    private static final long serialVersionUID = 4938790165047335376L;

    public PostIncrement() {
    }

    public PostIncrement(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    protected PostIncrement(PostIncrement proto) {
        super(proto);
        makeParentRoleValid();
    }

    public PostIncrement deepClone() {
        return new PostIncrement(this);
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
        v.visitPostIncrement(this);
    }
}
