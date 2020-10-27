package recoder.java.statement;

import recoder.java.*;

public class SynchronizedBlock extends JavaStatement implements StatementContainer, ExpressionContainer {
    private static final long serialVersionUID = -9179480508765855081L;

    protected Expression expression;

    protected StatementBlock body;

    public SynchronizedBlock() {
    }

    public SynchronizedBlock(StatementBlock body) {
        setBody(body);
        makeParentRoleValid();
    }

    public SynchronizedBlock(Expression e, StatementBlock body) {
        setExpression(e);
        setBody(body);
        makeParentRoleValid();
    }

    protected SynchronizedBlock(SynchronizedBlock proto) {
        super(proto);
        if (proto.expression != null)
            this.expression = proto.expression.deepClone();
        if (proto.body != null)
            this.body = proto.body.deepClone();
        makeParentRoleValid();
    }

    public SynchronizedBlock deepClone() {
        return new SynchronizedBlock(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.body != null)
            this.body.setStatementContainer(this);
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
        if (this.body == p) {
            StatementBlock r = (StatementBlock) q;
            this.body = r;
            if (r != null)
                r.setStatementContainer(this);
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

    public void setExpression(Expression e) {
        this.expression = e;
    }

    public int getChildCount() {
        int result = 0;
        if (this.expression != null)
            result++;
        if (this.body != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.expression != null) {
            if (index == 0)
                return this.expression;
            index--;
        }
        if (this.body != null &&
                index == 0)
            return this.body;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.expression == child)
            return 0;
        if (this.body == child)
            return 1;
        return -1;
    }

    public StatementBlock getBody() {
        return this.body;
    }

    public void setBody(StatementBlock body) {
        this.body = body;
    }

    public int getStatementCount() {
        return (this.body != null) ? 1 : 0;
    }

    public Statement getStatementAt(int index) {
        if (this.body != null && index == 0)
            return this.body;
        throw new ArrayIndexOutOfBoundsException();
    }

    public void accept(SourceVisitor v) {
        v.visitSynchronizedBlock(this);
    }
}
