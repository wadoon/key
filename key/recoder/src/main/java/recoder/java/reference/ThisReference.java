package recoder.java.reference;

import recoder.java.*;

public class ThisReference extends JavaNonTerminalProgramElement implements Reference, Expression, ReferencePrefix, ReferenceSuffix, TypeReferenceContainer {
    private static final long serialVersionUID = 6068045198408155115L;

    protected ExpressionContainer expressionParent;

    protected ReferenceSuffix referenceParent;

    protected TypeReference prefix;

    public ThisReference() {
        makeParentRoleValid();
    }

    public ThisReference(TypeReference outer) {
        setReferencePrefix(outer);
        makeParentRoleValid();
    }

    protected ThisReference(ThisReference proto) {
        super(proto);
        if (proto.prefix != null)
            this.prefix = proto.prefix.deepClone();
        makeParentRoleValid();
    }

    public ThisReference deepClone() {
        return new ThisReference(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.prefix != null)
            this.prefix.setReferenceSuffix(this);
    }

    public SourceElement getFirstElement() {
        return (this.prefix == null) ? this : this.prefix.getFirstElement();
    }

    public NonTerminalProgramElement getASTParent() {
        if (this.expressionParent != null)
            return this.expressionParent;
        return this.referenceParent;
    }

    public int getChildCount() {
        return (this.prefix != null) ? 1 : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (this.prefix != null &&
                index == 0)
            return this.prefix;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.prefix == child)
            return 0;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.prefix == p) {
            TypeReference r = (TypeReference) q;
            this.prefix = r;
            if (r != null)
                r.setReferenceSuffix(this);
            return true;
        }
        return false;
    }

    public ReferencePrefix getReferencePrefix() {
        return this.prefix;
    }

    public void setReferencePrefix(ReferencePrefix x) {
        this.prefix = (TypeReference) x;
    }

    public ReferenceSuffix getReferenceSuffix() {
        return this.referenceParent;
    }

    public void setReferenceSuffix(ReferenceSuffix path) {
        this.referenceParent = path;
    }

    public ExpressionContainer getExpressionContainer() {
        return this.expressionParent;
    }

    public void setExpressionContainer(ExpressionContainer c) {
        this.expressionParent = c;
    }

    public int getTypeReferenceCount() {
        return (this.prefix != null) ? 1 : 0;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (this.prefix != null && index == 0)
            return this.prefix;
        throw new ArrayIndexOutOfBoundsException();
    }

    public void accept(SourceVisitor v) {
        v.visitThisReference(this);
    }
}
