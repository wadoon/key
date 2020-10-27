package recoder.java.reference;

import recoder.java.*;

public class MetaClassReference extends JavaNonTerminalProgramElement implements Reference, Expression, ReferencePrefix, ReferenceSuffix, TypeReferenceContainer {
    private static final long serialVersionUID = -8591872994615086270L;

    protected ExpressionContainer expressionParent;

    protected ReferenceSuffix referenceParent;

    protected TypeReference typeReference;

    public MetaClassReference() {
    }

    public MetaClassReference(TypeReference reference) {
        setTypeReference(reference);
        makeParentRoleValid();
    }

    protected MetaClassReference(MetaClassReference proto) {
        super(proto);
        if (proto.typeReference != null)
            this.typeReference = proto.typeReference.deepClone();
        makeParentRoleValid();
    }

    public MetaClassReference deepClone() {
        return new MetaClassReference(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.typeReference != null)
            this.typeReference.setParent(this);
    }

    public NonTerminalProgramElement getASTParent() {
        if (this.referenceParent != null)
            return this.referenceParent;
        return this.expressionParent;
    }

    public int getChildCount() {
        return (this.typeReference != null) ? 1 : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (this.typeReference != null &&
                index == 0)
            return this.typeReference;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.typeReference == child)
            return 0;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.typeReference == p) {
            TypeReference r = (TypeReference) q;
            this.typeReference = r;
            if (r != null)
                r.setReferenceSuffix(this);
            return true;
        }
        return false;
    }

    public ReferenceSuffix getReferenceSuffix() {
        return this.referenceParent;
    }

    public void setReferenceSuffix(ReferenceSuffix path) {
        this.referenceParent = path;
    }

    public ReferencePrefix getReferencePrefix() {
        return this.typeReference;
    }

    public void setReferencePrefix(ReferencePrefix accessPath) {
        this.typeReference = (TypeReference) accessPath;
    }

    public ExpressionContainer getExpressionContainer() {
        return this.expressionParent;
    }

    public void setExpressionContainer(ExpressionContainer c) {
        this.expressionParent = c;
    }

    public int getTypeReferenceCount() {
        return (this.typeReference != null) ? 1 : 0;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (this.typeReference != null && index == 0)
            return this.typeReference;
        throw new ArrayIndexOutOfBoundsException();
    }

    public TypeReference getTypeReference() {
        return this.typeReference;
    }

    public void setTypeReference(TypeReference ref) {
        this.typeReference = ref;
    }

    public SourceElement getFirstElement() {
        return (this.typeReference == null) ? this : this.typeReference.getFirstElement();
    }

    public void accept(SourceVisitor v) {
        v.visitMetaClassReference(this);
    }
}
