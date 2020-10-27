package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class Modulo extends Operator {
    private static final long serialVersionUID = -7252952240290731650L;

    public Modulo() {
    }

    public Modulo(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected Modulo(Modulo proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Modulo deepClone() {
        return new Modulo(this);
    }

    public int getArity() {
        return 2;
    }

    public int getPrecedence() {
        return 2;
    }

    public int getNotation() {
        return 1;
    }

    public void accept(SourceVisitor v) {
        v.visitModulo(this);
    }
}
