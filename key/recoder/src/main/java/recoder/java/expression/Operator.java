package recoder.java.expression;

import recoder.java.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public abstract class Operator extends JavaNonTerminalProgramElement implements Expression, ExpressionContainer {
    public static final int PREFIX = 0;
    public static final int INFIX = 1;
    public static final int POSTFIX = 2;
    protected ExpressionContainer expressionParent;
    protected ASTList<Expression> children;

    public Operator() {
    }

    public Operator(Expression unaryChild) {
        this.children = (ASTList<Expression>) new ASTArrayList(getArity());
        this.children.add(unaryChild);
    }

    public Operator(Expression lhs, Expression rhs) {
        this.children = (ASTList<Expression>) new ASTArrayList(getArity());
        this.children.add(lhs);
        this.children.add(rhs);
    }

    protected Operator(Operator proto) {
        super(proto);
        if (proto.children != null)
            this.children = proto.children.deepClone();
    }

    public static boolean precedes(Operator a, Operator b) {
        return (a.getPrecedence() < b.getPrecedence());
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.children != null)
            for (int i = this.children.size() - 1; i >= 0; i--)
                this.children.get(i).setExpressionContainer(this);
    }

    public abstract int getArity();

    public abstract int getPrecedence();

    public abstract int getNotation();

    public boolean isLeftAssociative() {
        return true;
    }

    public SourceElement getFirstElement() {
        switch (getNotation()) {
            case 1:
            case 2:
                return this.children.get(0).getFirstElement();
        }
        return this;
    }

    public SourceElement getLastElement() {
        switch (getNotation()) {
            case 0:
            case 1:
                return this.children.get(getArity() - 1).getLastElement();
        }
        return this;
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

    public boolean isToBeParenthesized() {
        return (this.expressionParent instanceof Operator && !(this.expressionParent instanceof recoder.java.reference.ReferencePrefix) && ((Operator) this.expressionParent).getPrecedence() < getPrecedence());
    }
}
