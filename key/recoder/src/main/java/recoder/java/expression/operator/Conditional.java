package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public class Conditional extends Operator {
    private static final long serialVersionUID = -3581491297079611854L;

    public Conditional() {
    }

    public Conditional(Expression guard, Expression thenExpr, Expression elseExpr) {
        this.children = (ASTList) new ASTArrayList(getArity());
        this.children.add(guard);
        this.children.add(thenExpr);
        this.children.add(elseExpr);
        makeParentRoleValid();
    }

    protected Conditional(Conditional proto) {
        super(proto);
        makeParentRoleValid();
    }

    public Conditional deepClone() {
        return new Conditional(this);
    }

    public int getArity() {
        return 3;
    }

    public int getPrecedence() {
        return 12;
    }

    public int getNotation() {
        return 1;
    }

    public boolean isLeftAssociative() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitConditional(this);
    }
}
