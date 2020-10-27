package recoder.java.reference;

import recoder.java.*;

public class FieldReference extends VariableReference implements MemberReference, ReferenceSuffix, TypeReferenceContainer, ExpressionContainer {
    private static final long serialVersionUID = -1475141413582182288L;

    protected ReferencePrefix prefix;

    public FieldReference() {
    }

    public FieldReference(Identifier id) {
        super(id);
    }

    public FieldReference(ReferencePrefix prefix, Identifier id) {
        super(id);
        setReferencePrefix(prefix);
        makeParentRoleValid();
    }

    protected FieldReference(FieldReference proto) {
        super(proto);
        if (proto.prefix != null)
            this.prefix = (ReferencePrefix) proto.prefix.deepClone();
        makeParentRoleValid();
    }

    public FieldReference deepClone() {
        return new FieldReference(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.prefix != null)
            this.prefix.setReferenceSuffix(this);
    }

    public int getChildCount() {
        int result = 0;
        if (this.prefix != null)
            result++;
        if (this.name != null)
            result++;
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.prefix != null) {
            if (index == 0)
                return this.prefix;
            index--;
        }
        if (this.name != null &&
                index == 0)
            return this.name;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.prefix == child)
            return 0;
        if (this.name == child)
            return 1;
        return -1;
    }

    public ReferencePrefix getReferencePrefix() {
        return this.prefix;
    }

    public void setReferencePrefix(ReferencePrefix prefix) {
        this.prefix = prefix;
    }

    public int getTypeReferenceCount() {
        return (this.prefix instanceof TypeReference) ? 1 : 0;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (this.prefix instanceof TypeReference && index == 0)
            return (TypeReference) this.prefix;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getExpressionCount() {
        return (this.prefix instanceof Expression) ? 1 : 0;
    }

    public Expression getExpressionAt(int index) {
        if (this.prefix instanceof Expression && index == 0)
            return (Expression) this.prefix;
        throw new ArrayIndexOutOfBoundsException();
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.prefix == p) {
            ReferencePrefix r = (ReferencePrefix) q;
            this.prefix = r;
            if (r != null)
                r.setReferenceSuffix(this);
            return true;
        }
        if (this.name == p) {
            Identifier r = (Identifier) q;
            this.name = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        return false;
    }

    public SourceElement getFirstElement() {
        return (this.prefix == null) ? this.name : this.prefix.getFirstElement();
    }

    public void accept(SourceVisitor v) {
        v.visitFieldReference(this);
    }
}
