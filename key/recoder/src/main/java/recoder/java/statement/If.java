package recoder.java.statement;

import recoder.java.*;

public class If extends BranchStatement implements ExpressionContainer {
    private static final long serialVersionUID = -6352480723638689470L;

    protected Then thenBranch;

    protected Else elseBranch;

    protected Expression expression;

    public If() {
    }

    public If(Expression e, Statement thenStatement) {
        this(e, thenStatement, null);
    }

    public If(Expression e, Then thenBranch) {
        this(e, thenBranch, null);
    }

    public If(Expression e, Then thenBranch, Else elseBranch) {
        if (e == null)
            throw new NullPointerException();
        this.expression = e;
        setThen(thenBranch);
        setElse(elseBranch);
        makeParentRoleValid();
    }

    public If(Expression e, Statement thenStatement, Statement elseStatement) {
        if (e == null)
            throw new NullPointerException();
        this.expression = e;
        setThen(getFactory().createThen(thenStatement));
        if (elseStatement != null)
            setElse(getFactory().createElse(elseStatement));
        makeParentRoleValid();
    }

    protected If(If proto) {
        super(proto);
        if (proto.thenBranch != null)
            this.thenBranch = proto.thenBranch.deepClone();
        if (proto.elseBranch != null)
            this.elseBranch = proto.elseBranch.deepClone();
        if (proto.expression != null)
            this.expression = proto.expression.deepClone();
        makeParentRoleValid();
    }

    public If deepClone() {
        return new If(this);
    }

    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }

    public int getChildCount() {
        int result = 0;
        if (this.expression != null)
            result++;
        if (this.thenBranch != null)
            result++;
        if (this.elseBranch != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.expression != null) {
            if (index == 0)
                return this.expression;
            index--;
        }
        if (this.thenBranch != null) {
            if (index == 0)
                return this.thenBranch;
            index--;
        }
        if (this.elseBranch != null &&
                index == 0)
            return this.elseBranch;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.expression == child)
            return 0;
        if (this.thenBranch == child)
            return 1;
        if (this.elseBranch == child)
            return 2;
        return -1;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.expression != null)
            this.expression.setExpressionContainer(this);
        if (this.thenBranch != null)
            this.thenBranch.setParent(this);
        if (this.elseBranch != null)
            this.elseBranch.setParent(this);
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
        if (this.thenBranch == p) {
            Then r = (Then) q;
            this.thenBranch = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        if (this.elseBranch == p) {
            Else r = (Else) q;
            this.elseBranch = r;
            if (r != null)
                r.setParent(this);
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

    public Then getThen() {
        return this.thenBranch;
    }

    public void setThen(Then thenBranch) {
        this.thenBranch = thenBranch;
    }

    public Else getElse() {
        return this.elseBranch;
    }

    public void setElse(Else elseBranch) {
        this.elseBranch = elseBranch;
    }

    public int getBranchCount() {
        int result = 0;
        if (this.thenBranch != null)
            result++;
        if (this.elseBranch != null)
            result++;
        return result;
    }

    public Branch getBranchAt(int index) {
        if (this.thenBranch != null) {
            if (index == 0)
                return this.thenBranch;
            index--;
        }
        if (this.elseBranch != null &&
                index == 0)
            return this.elseBranch;
        throw new ArrayIndexOutOfBoundsException();
    }

    public void accept(SourceVisitor v) {
        v.visitIf(this);
    }
}
