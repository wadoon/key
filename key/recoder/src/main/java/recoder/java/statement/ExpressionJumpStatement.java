package recoder.java.statement;

import recoder.java.Expression;
import recoder.java.ExpressionContainer;
import recoder.java.ProgramElement;

public abstract class ExpressionJumpStatement extends JumpStatement implements ExpressionContainer {
    protected Expression expression;

    public ExpressionJumpStatement() {
    }

    public ExpressionJumpStatement(Expression expr) {
        if (expr != null)
            setExpression(expr);
    }

    protected ExpressionJumpStatement(ExpressionJumpStatement proto) {
        super(proto);
        if (proto.expression != null)
            this.expression = proto.expression.deepClone();
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.expression != null)
            this.expression.setExpressionContainer(this);
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.expression == p) {
            Expression r = (Expression) q;
            this.expression = r;
            if (r != null)
                r.setExpressionContainer(this);
            return true;
        }
        return false;
    }

    public int getExpressionCount() {
        return (this.expression != null) ? 1 : 0;
    }

    public Expression getExpressionAt(int index) {
        if (this.expression != null && index == 0)
            return this.expression;
        throw new ArrayIndexOutOfBoundsException();
    }

    public Expression getExpression() {
        return this.expression;
    }

    public void setExpression(Expression expr) {
        this.expression = expr;
    }

    public int getChildCount() {
        return (this.expression != null) ? 1 : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (this.expression != null &&
                index == 0)
            return this.expression;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.expression == child)
            return 0;
        return -1;
    }
}
