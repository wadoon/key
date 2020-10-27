package recoder.java.expression;

import recoder.java.*;
import recoder.list.generic.ASTList;

public class ArrayInitializer extends JavaNonTerminalProgramElement implements Expression, ExpressionContainer {
    private static final long serialVersionUID = 7171507009155916797L;

    protected ExpressionContainer expressionParent;

    protected ASTList<Expression> children;

    public ArrayInitializer() {
    }

    public ArrayInitializer(ASTList<Expression> args) {
        setArguments(args);
        makeParentRoleValid();
    }

    protected ArrayInitializer(ArrayInitializer proto) {
        super(proto);
        if (proto.children != null)
            this.children = proto.children.deepClone();
        makeParentRoleValid();
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.children != null)
            for (int i = this.children.size() - 1; i >= 0; i--)
                this.children.get(i).setExpressionContainer(this);
    }

    public ArrayInitializer deepClone() {
        return new ArrayInitializer(this);
    }

    public NonTerminalProgramElement getASTParent() {
        return this.expressionParent;
    }

    public int getChildCount() {
        return (this.children != null) ? this.children.size() : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (this.children != null)
            return this.children.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.children != null) {
            int index = this.children.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        return -1;
    }

    public ExpressionContainer getExpressionContainer() {
        return this.expressionParent;
    }

    public void setExpressionContainer(ExpressionContainer c) {
        this.expressionParent = c;
    }

    public int getExpressionCount() {
        return (this.children != null) ? this.children.size() : 0;
    }

    public Expression getExpressionAt(int index) {
        if (this.children != null)
            return this.children.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        int count = (this.children == null) ? 0 : this.children.size();
        for (int i = 0; i < count; i++) {
            if (this.children.get(i) == p) {
                if (q == null) {
                    this.children.remove(i);
                } else {
                    Expression r = (Expression) q;
                    this.children.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        return false;
    }

    public ASTList<Expression> getArguments() {
        return this.children;
    }

    public void setArguments(ASTList<Expression> list) {
        this.children = list;
    }

    public void accept(SourceVisitor v) {
        v.visitArrayInitializer(this);
    }
}
