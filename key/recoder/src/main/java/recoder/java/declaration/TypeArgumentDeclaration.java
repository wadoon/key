package recoder.java.declaration;

import recoder.abstraction.TypeArgument;
import recoder.convenience.Naming;
import recoder.java.*;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.list.generic.ASTList;

public class TypeArgumentDeclaration extends JavaNonTerminalProgramElement implements TypeReferenceContainer, TypeArgument {
    private static final long serialVersionUID = -8369885569636132718L;

    protected TypeReference typeReference;

    protected TypeArgument.WildcardMode wildcardMode;

    protected Reference parent;

    public TypeArgumentDeclaration() {
        this(null, TypeArgument.WildcardMode.Any);
    }

    protected TypeArgumentDeclaration(TypeArgumentDeclaration proto) {
        super(proto);
        this.wildcardMode = proto.wildcardMode;
        if (proto.typeReference != null)
            this.typeReference = proto.typeReference.deepClone();
        makeParentRoleValid();
    }

    public TypeArgumentDeclaration(TypeReference tr) {
        this(tr, TypeArgument.WildcardMode.None);
    }

    public TypeArgumentDeclaration(TypeReference tr, TypeArgument.WildcardMode wm) {
        this.typeReference = tr;
        this.wildcardMode = wm;
        makeParentRoleValid();
    }

    public int getTypeReferenceCount() {
        return (this.typeReference == null) ? 0 : 1;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (index == 0 && this.typeReference != null)
            return this.typeReference;
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public int getChildCount() {
        return getTypeReferenceCount();
    }

    public ProgramElement getChildAt(int index) {
        return getTypeReferenceAt(index);
    }

    public int getChildPositionCode(ProgramElement child) {
        if (child == this.typeReference)
            return 0;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (p == this.typeReference) {
            this.typeReference = (TypeReference) q;
            if (this.typeReference != null)
                this.typeReference.setParent(this);
            return true;
        }
        return false;
    }

    public NonTerminalProgramElement getASTParent() {
        return (NonTerminalProgramElement) this.parent;
    }

    public Reference getParent() {
        return this.parent;
    }

    public void setParent(Reference tr) {
        this.parent = tr;
        if (!(tr instanceof TypeReference) && !(tr instanceof recoder.java.reference.UncollatedReferenceQualifier) && !(tr instanceof recoder.java.reference.MethodReference))
            throw new IllegalArgumentException();
    }

    public void accept(SourceVisitor v) {
        v.visitTypeArgument(this);
    }

    public TypeArgumentDeclaration deepClone() {
        return new TypeArgumentDeclaration(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.typeReference != null)
            this.typeReference.setParent(this);
    }

    public TypeArgument.WildcardMode getWildcardMode() {
        return this.wildcardMode;
    }

    public void setWildcardMode(TypeArgument.WildcardMode wm) {
        this.wildcardMode = wm;
    }

    public String getTypeName() {
        return Naming.toPathName(this.typeReference);
    }

    public ASTList<TypeArgumentDeclaration> getTypeArguments() {
        if (this.wildcardMode == TypeArgument.WildcardMode.Any)
            return null;
        return this.typeReference.getTypeArguments();
    }

    public TypeReference getTypeReference() {
        return this.typeReference;
    }

    public void setTypeReference(TypeReference tr) {
        this.typeReference = tr;
    }

    public SourceElement getFirstElement() {
        if (this.wildcardMode != TypeArgument.WildcardMode.None)
            return this;
        return (this.typeReference == null) ? this : this.typeReference.getFirstElement();
    }
}
