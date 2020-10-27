package recoder.java.statement;

import recoder.java.*;
import recoder.list.generic.ASTList;

public class Case extends Branch implements ExpressionContainer {
    private static final long serialVersionUID = 4344680443480425524L;

    protected Expression expression;

    protected ASTList<Statement> body;

    public Case() {
    }

    public Case(Expression e) {
        setExpression(e);
        makeParentRoleValid();
    }

    public Case(Expression e, ASTList<Statement> body) {
        setBody(body);
        setExpression(e);
        makeParentRoleValid();
    }

    protected Case(Case proto) {
        super(proto);
        if (proto.expression != null)
            this.expression = proto.expression.deepClone();
        if (proto.body != null)
            this.body = proto.body.deepClone();
        makeParentRoleValid();
    }

    public Case deepClone() {
        return new Case(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.expression != null)
            this.expression.setExpressionContainer(this);
        if (this.body != null)
            for (int i = 0; i < this.body.size(); i++)
                this.body.get(i).setStatementContainer(this);
    }

    public Switch getParent() {
        return (Switch) this.parent;
    }

    public void setParent(Switch parent) {
        this.parent = parent;
    }

    public int getChildCount() {
        int result = 0;
        if (this.expression != null)
            result++;
        if (this.body != null)
            result += this.body.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.expression != null) {
            if (index == 0)
                return this.expression;
            index--;
        }
        if (this.body != null) {
            int len = this.body.size();
            if (len > index)
                return this.body.get(index);
            index -= len;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.expression == child)
            return 0;
        if (this.body != null) {
            int index = this.body.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x1;
        }
        return -1;
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
        int count = (this.body == null) ? 0 : this.body.size();
        for (int i = 0; i < count; i++) {
            if (this.body.get(i) == p) {
                if (q == null) {
                    this.body.remove(i);
                } else {
                    Statement r = (Statement) q;
                    this.body.set(i, r);
                    r.setStatementContainer(this);
                }
                return true;
            }
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

    public int getStatementCount() {
        return (this.body != null) ? this.body.size() : 0;
    }

    public Statement getStatementAt(int index) {
        if (this.body != null)
            return this.body.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public Expression getExpression() {
        return this.expression;
    }

    public void setExpression(Expression e) {
        if (e == null)
            throw new NullPointerException("Cases must have an expression");
        this.expression = e;
    }

    public ASTList<Statement> getBody() {
        return this.body;
    }

    public void setBody(ASTList<Statement> list) {
        this.body = list;
    }

    public void accept(SourceVisitor v) {
        v.visitCase(this);
    }

    public SourceElement getLastElement() {
        if (this.body == null || this.body.size() == 0)
            return this;
        return this.body.get(this.body.size() - 1).getLastElement();
    }
}
