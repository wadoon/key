package recoder.java.reference;

import recoder.java.*;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.list.generic.ASTList;

public class UncollatedReferenceQualifier extends JavaNonTerminalProgramElement implements TypeReferenceInfix, ExpressionContainer, TypeReferenceContainer, PackageReferenceContainer, Reference, Expression {
    private static final long serialVersionUID = -1896030875000030810L;

    protected NonTerminalProgramElement parent;

    protected ReferenceSuffix suffix;

    protected ReferencePrefix prefix;

    protected ASTList<TypeArgumentDeclaration> typeArguments;

    protected Identifier name;

    public UncollatedReferenceQualifier() {
    }

    public UncollatedReferenceQualifier(Identifier id) {
        setIdentifier(id);
        makeParentRoleValid();
    }

    public UncollatedReferenceQualifier(ReferencePrefix prefix, Identifier id) {
        setIdentifier(id);
        setReferencePrefix(prefix);
        makeParentRoleValid();
    }

    protected UncollatedReferenceQualifier(UncollatedReferenceQualifier proto) {
        super(proto);
        if (proto.prefix != null)
            this.prefix = (ReferencePrefix) proto.prefix.deepClone();
        if (proto.name != null)
            this.name = proto.name.deepClone();
        if (proto.typeArguments != null)
            this.typeArguments = proto.typeArguments.deepClone();
        makeParentRoleValid();
    }

    public UncollatedReferenceQualifier deepClone() {
        return new UncollatedReferenceQualifier(this);
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
        return (this.parent != null) ? this.parent : this.suffix;
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

    public ExpressionContainer getExpressionContainer() {
        if (this.parent instanceof ExpressionContainer)
            return (ExpressionContainer) this.parent;
        return null;
    }

    public void setExpressionContainer(ExpressionContainer c) {
        this.parent = c;
        this.suffix = null;
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

    public PackageReference getPackageReference() {
        return (this.prefix instanceof PackageReference) ? (PackageReference) this.prefix : null;
    }

    public int getExpressionCount() {
        return (this.prefix instanceof Expression) ? 1 : 0;
    }

    public Expression getExpressionAt(int index) {
        if (this.prefix instanceof Expression && index == 0)
            return (Expression) this.prefix;
        throw new ArrayIndexOutOfBoundsException();
    }

    public ReferencePrefix getReferencePrefix() {
        return this.prefix;
    }

    public void setReferencePrefix(ReferencePrefix prefix) {
        this.prefix = prefix;
    }

    public ReferenceSuffix getReferenceSuffix() {
        return this.suffix;
    }

    public void setReferenceSuffix(ReferenceSuffix x) {
        this.suffix = x;
        this.parent = null;
    }

    public void setParent(Import imp) {
        this.parent = imp;
        this.suffix = null;
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

    private void copySourceInfos(Reference ref) {
        ref.setRelativePosition(getRelativePosition());
        ref.setStartPosition(getStartPosition());
        ref.setEndPosition(getEndPosition());
        ref.setComments(this.comments);
    }

    public ArrayLengthReference toArrayLengthReference() {
        ArrayLengthReference ref = getFactory().createArrayLengthReference();
        ref.setExpressionContainer(getExpressionContainer());
        ref.setReferencePrefix(this.prefix);
        copySourceInfos(ref);
        ref.makeParentRoleValid();
        return ref;
    }

    public VariableReference toVariableReference() {
        VariableReference ref = getFactory().createVariableReference();
        ref.setExpressionContainer(getExpressionContainer());
        ref.setReferenceSuffix(getReferenceSuffix());
        ref.setIdentifier(this.name);
        copySourceInfos(ref);
        ref.makeParentRoleValid();
        return ref;
    }

    public VariableReference toFieldReference() {
        FieldReference ref = getFactory().createFieldReference();
        ref.setExpressionContainer(getExpressionContainer());
        ref.setReferenceSuffix(getReferenceSuffix());
        ref.setReferencePrefix(this.prefix);
        ref.setIdentifier(this.name);
        copySourceInfos(ref);
        ref.makeParentRoleValid();
        return ref;
    }

    public TypeReference toTypeReference() {
        TypeReference ref = getFactory().createTypeReference();
        ref.setReferenceSuffix(getReferenceSuffix());
        ref.setReferencePrefix(this.prefix);
        ref.setIdentifier(this.name);
        ref.setTypeArguments(this.typeArguments);
        ref.makeParentRoleValid();
        copySourceInfos(ref);
        ref.makeParentRoleValid();
        return ref;
    }

    public PackageReference toPackageReference() {
        if (this.prefix instanceof UncollatedReferenceQualifier)
            this.prefix = ((UncollatedReferenceQualifier) this.prefix).toPackageReference();
        PackageReference ref = getFactory().createPackageReference();
        ref.setReferenceSuffix(getReferenceSuffix());
        ref.setReferencePrefix(this.prefix);
        ref.setIdentifier(this.name);
        copySourceInfos(ref);
        ref.makeParentRoleValid();
        return ref;
    }

    public void accept(SourceVisitor v) {
        v.visitUncollatedReferenceQualifier(this);
    }

    public ASTList<TypeArgumentDeclaration> getTypeArguments() {
        return this.typeArguments;
    }

    public void setTypeArguments(ASTList<TypeArgumentDeclaration> ta) {
        this.typeArguments = ta;
    }
}
