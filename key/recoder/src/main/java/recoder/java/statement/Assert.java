package recoder.java.statement;

import recoder.java.*;

public class Assert extends JavaStatement implements ExpressionContainer {
    private static final long serialVersionUID = -5203926244893543507L;

    protected Expression condition;

    protected Expression message;

    public Assert() {
    }

    public Assert(Expression cond) {
        this(cond, null);
    }

    public Assert(Expression cond, Expression msg) {
        if (cond == null)
            throw new NullPointerException();
        this.condition = cond;
        this.message = msg;
        makeParentRoleValid();
    }

    protected Assert(Assert proto) {
        super(proto);
        if (proto.condition != null)
            this.condition = proto.condition.deepClone();
        if (proto.message != null)
            this.message = proto.message.deepClone();
        makeParentRoleValid();
    }

    public Assert deepClone() {
        return new Assert(this);
    }

    public SourceElement getLastElement() {
        return (this.message != null) ? this.message.getLastElement() : this.condition.getLastElement();
    }

    public int getChildCount() {
        int result = 0;
        if (this.condition != null)
            result++;
        if (this.message != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.condition != null) {
            if (index == 0)
                return this.condition;
            index--;
        }
        if (this.message != null &&
                index == 0)
            return this.message;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.condition == child)
            return 0;
        if (this.message == child)
            return 1;
        return -1;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.condition != null)
            this.condition.setExpressionContainer(this);
        if (this.message != null)
            this.message.setExpressionContainer(this);
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.condition == p) {
            Expression r = (Expression) q;
            this.condition = r;
            if (r != null)
                r.setExpressionContainer(this);
            return true;
        }
        if (this.message == p) {
            Expression r = (Expression) q;
            this.message = r;
            if (r != null)
                r.setExpressionContainer(this);
            return true;
        }
        return false;
    }

    public int getExpressionCount() {
        int c = 0;
        if (this.condition != null)
            c++;
        if (this.message != null)
            c++;
        return c;
    }

    public Expression getExpressionAt(int index) {
        if (this.condition != null) {
            if (index == 0)
                return this.condition;
            index--;
        }
        if (this.message != null &&
                index == 0)
            return this.message;
        throw new ArrayIndexOutOfBoundsException();
    }

    public Expression getCondition() {
        return this.condition;
    }

    public void setCondition(Expression expr) {
        this.condition = expr;
    }

    public Expression getMessage() {
        return this.message;
    }

    public void setMessage(Expression expr) {
        this.message = expr;
    }

    public void accept(SourceVisitor v) {
        v.visitAssert(this);
    }
}
