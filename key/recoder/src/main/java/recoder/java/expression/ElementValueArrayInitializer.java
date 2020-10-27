package recoder.java.expression;

import recoder.java.*;
import recoder.list.generic.ASTList;

public class ElementValueArrayInitializer extends JavaNonTerminalProgramElement implements Expression, ExpressionContainer {
    private static final long serialVersionUID = -3857746318263472090L;

    protected ExpressionContainer parent;

    protected ASTList<Expression> elementValues;

    public ElementValueArrayInitializer() {
    }

    protected ElementValueArrayInitializer(ElementValueArrayInitializer proto) {
        super(proto);
        if (proto.elementValues != null)
            this.elementValues = proto.elementValues.deepClone();
    }

    public ExpressionContainer getExpressionContainer() {
        return this.parent;
    }

    public void setExpressionContainer(ExpressionContainer c) {
        this.parent = c;
    }

    public ElementValueArrayInitializer deepClone() {
        return new ElementValueArrayInitializer(this);
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public void accept(SourceVisitor v) {
        v.visitElementValueArrayInitializer(this);
    }

    public int getExpressionCount() {
        return (this.elementValues == null) ? 0 : this.elementValues.size();
    }

    public Expression getExpressionAt(int index) {
        if (this.elementValues != null)
            return this.elementValues.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildCount() {
        return getExpressionCount();
    }

    public ProgramElement getChildAt(int index) {
        return getExpressionAt(index);
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.elementValues == null)
            return -1;
        int idx = this.elementValues.indexOf(child);
        if (idx != -1)
            return idx << 4;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        int count = (this.elementValues == null) ? 0 : this.elementValues.size();
        for (int i = 0; i < count; i++) {
            if (this.elementValues.get(i) == p) {
                if (q == null) {
                    this.elementValues.remove(i);
                } else {
                    Expression r = (Expression) q;
                    this.elementValues.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        return false;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.elementValues != null)
            for (Expression e : this.elementValues)
                e.setExpressionContainer(this);
    }

    public ASTList<Expression> getElementValues() {
        return this.elementValues;
    }

    public void setElementValues(ASTList<Expression> elementValues) {
        this.elementValues = elementValues;
    }
}
