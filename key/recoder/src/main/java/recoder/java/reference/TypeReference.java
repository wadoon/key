package recoder.java.reference;

import recoder.java.*;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.list.generic.ASTList;

public class TypeReference extends JavaNonTerminalProgramElement implements TypeReferenceInfix, TypeReferenceContainer, PackageReferenceContainer, MemberReference {
    private static final long serialVersionUID = -8415845940952618808L;

    protected TypeReferenceContainer parent;

    protected ReferencePrefix prefix;

    protected int dimensions;

    protected ASTList<TypeArgumentDeclaration> typeArguments;

    protected Identifier name;

    public TypeReference() {
    }

    public TypeReference(Identifier name) {
        setIdentifier(name);
        makeParentRoleValid();
    }

    public TypeReference(ReferencePrefix prefix, Identifier name) {
        setIdentifier(name);
        setReferencePrefix(prefix);
        makeParentRoleValid();
    }

    public TypeReference(Identifier name, int dim) {
        setIdentifier(name);
        setDimensions(dim);
        makeParentRoleValid();
    }

    public TypeReference(Identifier name, ASTList<TypeArgumentDeclaration> typeArgs) {
        setIdentifier(name);
        this.typeArguments = typeArgs;
        makeParentRoleValid();
    }

    protected TypeReference(TypeReference proto) {
        super(proto);
        if (proto.prefix != null)
            this.prefix = (ReferencePrefix) proto.prefix.deepClone();
        if (proto.name != null)
            this.name = proto.name.deepClone();
        if (proto.typeArguments != null)
            this.typeArguments = proto.typeArguments.deepClone();
        this.dimensions = proto.dimensions;
        makeParentRoleValid();
    }

    public TypeReference deepClone() {
        return new TypeReference(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.prefix != null)
            this.prefix.setReferenceSuffix(this);
        if (this.name != null)
            this.name.setParent(this);
        if (this.typeArguments != null)
            for (TypeArgumentDeclaration ta : this.typeArguments)
                ta.setParent(this);
    }

    public SourceElement getFirstElement() {
        return (this.prefix == null) ? this.name : this.prefix.getFirstElement();
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public int getChildCount() {
        int result = 0;
        if (this.prefix != null)
            result++;
        if (this.name != null)
            result++;
        if (this.typeArguments != null)
            result += this.typeArguments.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.prefix != null) {
            if (index == 0)
                return this.prefix;
            index--;
        }
        if (this.name != null) {
            if (index == 0)
                return this.name;
            index--;
        }
        if (this.typeArguments != null)
            return this.typeArguments.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.prefix == child)
            return 0;
        if (this.name == child)
            return 1;
        if (this.typeArguments != null) {
            int idx = this.typeArguments.indexOf(child);
            if (idx != -1)
                return idx << 4 | 0x2;
        }
        return -1;
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
        if (this.typeArguments != null) {
            int idx = this.typeArguments.indexOf(p);
            if (idx != -1) {
                if (q == null) {
                    this.typeArguments.remove(idx);
                } else {
                    this.typeArguments.set(idx, q);
                    ((TypeArgumentDeclaration) q).setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    public TypeReferenceContainer getParent() {
        return this.parent;
    }

    public void setParent(TypeReferenceContainer elem) {
        this.parent = elem;
    }

    public ReferencePrefix getReferencePrefix() {
        return this.prefix;
    }

    public void setReferencePrefix(ReferencePrefix x) {
        this.prefix = x;
    }

    public PackageReference getPackageReference() {
        return (this.prefix instanceof PackageReference) ? (PackageReference) this.prefix : null;
    }

    public ReferenceSuffix getReferenceSuffix() {
        return (this.parent instanceof ReferenceSuffix) ? (ReferenceSuffix) this.parent : null;
    }

    public void setReferenceSuffix(ReferenceSuffix x) {
        this.parent = (TypeReferenceContainer) x;
    }

    public int getDimensions() {
        return this.dimensions;
    }

    public void setDimensions(int dim) {
        this.dimensions = dim;
    }

    public final String getName() {
        return (this.name == null) ? null : this.name.getText();
    }

    public Identifier getIdentifier() {
        return this.name;
    }

    public void setIdentifier(Identifier id) {
        this.name = id;
    }

    public void accept(SourceVisitor v) {
        v.visitTypeReference(this);
    }

    public ASTList<TypeArgumentDeclaration> getTypeArguments() {
        return this.typeArguments;
    }

    public void setTypeArguments(ASTList<TypeArgumentDeclaration> ta) {
        this.typeArguments = ta;
    }
}
