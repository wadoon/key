package recoder.java.reference;

import recoder.java.*;
import recoder.list.generic.ASTList;

public abstract class SpecialConstructorReference extends JavaNonTerminalProgramElement implements ConstructorReference {
    protected StatementContainer parent;

    protected ASTList<Expression> arguments;

    public SpecialConstructorReference() {
    }

    public SpecialConstructorReference(ASTList<Expression> arguments) {
        setArguments(arguments);
    }

    protected SpecialConstructorReference(SpecialConstructorReference proto) {
        super(proto);
        if (proto.arguments != null)
            this.arguments = proto.arguments.deepClone();
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.arguments != null)
            for (int i = this.arguments.size() - 1; i >= 0; i--)
                this.arguments.get(i).setExpressionContainer(this);
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public StatementContainer getStatementContainer() {
        return this.parent;
    }

    public void setStatementContainer(StatementContainer s) {
        this.parent = s;
    }

    public int getChildCount() {
        return (this.arguments != null) ? this.arguments.size() : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (this.arguments != null)
            return this.arguments.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getExpressionCount() {
        return (this.arguments != null) ? this.arguments.size() : 0;
    }

    public Expression getExpressionAt(int index) {
        if (this.arguments != null)
            return this.arguments.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        int count = (this.arguments == null) ? 0 : this.arguments.size();
        for (int i = 0; i < count; i++) {
            if (this.arguments.get(i) == p) {
                if (q == null) {
                    this.arguments.remove(i);
                } else {
                    Expression r = (Expression) q;
                    this.arguments.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        return false;
    }

    public ASTList<Expression> getArguments() {
        return this.arguments;
    }

    public void setArguments(ASTList<Expression> list) {
        this.arguments = list;
    }
}
