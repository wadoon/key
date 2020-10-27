package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class BinaryNot extends Operator {
    private static final long serialVersionUID = 6494982658640409026L;

    public BinaryNot() {
    }

    public BinaryNot(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    protected BinaryNot(BinaryNot proto) {
        super(proto);
        makeParentRoleValid();
    }

    public BinaryNot deepClone() {
        return new BinaryNot(this);
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

    public boolean isLeftAssociative() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitBinaryNot(this);
    }
}
