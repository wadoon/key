package recoder.java.reference;

import recoder.java.*;

public class SuperReference extends JavaNonTerminalProgramElement implements Reference, Expression, ReferencePrefix, ReferenceSuffix, ExpressionContainer, TypeReferenceContainer {
    private static final long serialVersionUID = 1572767136419541150L;

    protected ExpressionContainer expressionParent;

    protected ReferenceSuffix referenceParent;

    protected ReferencePrefix accessPath;

    public SuperReference() {
        makeParentRoleValid();
    }

    public SuperReference(ReferencePrefix accessPath) {
        setReferencePrefix(accessPath);
        makeParentRoleValid();
    }

    protected SuperReference(SuperReference proto) {
        super(proto);
        if (proto.accessPath != null)
            this.accessPath = (ReferencePrefix) proto.accessPath.deepClone();
        makeParentRoleValid();
    }

    public SuperReference deepClone() {
        return new SuperReference(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.accessPath != null)
            this.accessPath.setReferenceSuffix(this);
    }

    public SourceElement getFirstElement() {
        return (this.accessPath == null) ? this : this.accessPath.getFirstElement();
    }

    public ReferencePrefix getReferencePrefix() {
        return this.accessPath;
    }

    public void setReferencePrefix(ReferencePrefix p) {
        this.accessPath = p;
    }

    public ReferenceSuffix getReferenceSuffix() {
        return this.referenceParent;
    }

    public void setReferenceSuffix(ReferenceSuffix x) {
        this.referenceParent = x;
    }

    public ExpressionContainer getExpressionContainer() {
        return this.expressionParent;
    }

    public void setExpressionContainer(ExpressionContainer c) {
        this.expressionParent = c;
    }

    public NonTerminalProgramElement getASTParent() {
        if (this.expressionParent != null)
            return this.expressionParent;
        return this.referenceParent;
    }

    public int getChildCount() {
        return (this.accessPath != null) ? 1 : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (this.accessPath != null &&
                index == 0)
            return this.accessPath;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.accessPath == child)
            return 0;
        return -1;
    }

    public int getExpressionCount() {
        return (this.accessPath instanceof Expression) ? 1 : 0;
    }

    public Expression getExpressionAt(int index) {
        if (this.accessPath instanceof Expression && index == 0)
            return (Expression) this.accessPath;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getTypeReferenceCount() {
        return (this.accessPath instanceof TypeReference) ? 1 : 0;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (this.accessPath instanceof TypeReference && index == 0)
            return (TypeReference) this.accessPath;
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
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitSuperReference(this);
    }
}
