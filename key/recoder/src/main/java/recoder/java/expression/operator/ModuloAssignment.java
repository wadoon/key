package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

public class ModuloAssignment extends Assignment {
    private static final long serialVersionUID = 4380772781463528921L;

    public ModuloAssignment() {
    }

    public ModuloAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    protected ModuloAssignment(ModuloAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    public ModuloAssignment deepClone() {
        return new ModuloAssignment(this);
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
        v.visitModuloAssignment(this);
    }
}
