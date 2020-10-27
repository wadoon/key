package recoder.java.reference;

import recoder.java.*;
import recoder.list.generic.ASTList;

public class ArrayReference extends JavaNonTerminalProgramElement implements Reference, Expression, ReferencePrefix, ReferenceSuffix, ExpressionContainer, TypeReferenceContainer {
    private static final long serialVersionUID = 5264208667205795216L;

    protected ReferenceSuffix accessParent;

    protected ExpressionContainer parent;

    protected ReferencePrefix accessPath;

    protected ASTList<Expression> inits;

    public ArrayReference() {
    }

    public ArrayReference(ReferencePrefix accessPath, ASTList<Expression> initializers) {
        setReferencePrefix(accessPath);
        setDimensionExpressions(initializers);
        makeParentRoleValid();
    }

    protected ArrayReference(ArrayReference proto) {
        super(proto);
        if (proto.accessPath != null)
            this.accessPath = (ReferencePrefix) proto.accessPath.deepClone();
        if (proto.inits != null)
            this.inits = proto.inits.deepClone();
        makeParentRoleValid();
    }

    public ArrayReference deepClone() {
        return new ArrayReference(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.accessPath != null)
            this.accessPath.setReferenceSuffix(this);
        if (this.inits != null)
            for (int i = this.inits.size() - 1; i >= 0; i--)
                this.inits.get(i).setExpressionContainer(this);
    }

    public NonTerminalProgramElement getASTParent() {
        if (this.parent != null)
            return this.parent;
        return this.accessParent;
    }

    public int getExpressionCount() {
        int c = 0;
        if (this.accessPath instanceof Expression)
            c++;
        if (this.inits != null)
            c += this.inits.size();
        return c;
    }

    public Expression getExpressionAt(int index) {
        if (this.accessPath instanceof Expression) {
            if (index == 0)
                return (Expression) this.accessPath;
            index--;
        }
        if (this.inits != null)
            return this.inits.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.accessPath == p) {
            ReferencePrefix r = (ReferencePrefix) q;
            this.accessPath = r;
            if (r != null)
                r.setReferenceSuffix(this);
            return true;
        }
        int count = (this.inits == null) ? 0 : this.inits.size();
        for (int i = 0; i < count; i++) {
            if (this.inits.get(i) == p) {
                if (q == null) {
                    this.inits.remove(i);
                } else {
                    Expression r = (Expression) q;
                    this.inits.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        return false;
    }

    public int getTypeReferenceCount() {
        return (this.accessPath instanceof TypeReference) ? 1 : 0;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (this.accessPath instanceof TypeReference && index == 0)
            return (TypeReference) this.accessPath;
        throw new ArrayIndexOutOfBoundsException();
    }

    public ReferenceSuffix getReferenceSuffix() {
        return this.accessParent;
    }

    public void setReferenceSuffix(ReferenceSuffix path) {
        this.accessParent = path;
    }

    public ReferencePrefix getReferencePrefix() {
        return this.accessPath;
    }

    public void setReferencePrefix(ReferencePrefix accessPath) {
        this.accessPath = accessPath;
    }

    public int getChildCount() {
        int result = 0;
        if (this.accessPath != null)
            result++;
        if (this.inits != null)
            result += this.inits.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.accessPath != null) {
            if (index == 0)
                return this.accessPath;
            index--;
        }
        if (this.inits != null)
            return this.inits.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.accessPath == child)
            return 0;
        if (this.inits != null) {
            int index = this.inits.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x1;
        }
        return -1;
    }

    public ExpressionContainer getExpressionContainer() {
        return this.parent;
    }

    public void setExpressionContainer(ExpressionContainer c) {
        this.parent = c;
    }

    public ASTList<Expression> getDimensionExpressions() {
        return this.inits;
    }

    public void setDimensionExpressions(ASTList<Expression> list) {
        this.inits = list;
    }

    public SourceElement getFirstElement() {
        return (this.accessPath == null) ? this : this.accessPath.getFirstElement();
    }

    public void accept(SourceVisitor v) {
        v.visitArrayReference(this);
    }
}
