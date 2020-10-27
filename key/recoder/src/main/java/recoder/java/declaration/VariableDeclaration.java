package recoder.java.declaration;

import recoder.java.SourceElement;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.list.generic.ASTList;

import java.util.List;

public abstract class VariableDeclaration extends JavaDeclaration implements TypeReferenceContainer {
    protected TypeReference typeReference;

    public VariableDeclaration() {
    }

    public VariableDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef) {
        setDeclarationSpecifiers(mods);
        setTypeReference(typeRef);
    }

    protected VariableDeclaration(VariableDeclaration proto) {
        super(proto);
        if (proto.typeReference != null)
            this.typeReference = proto.typeReference.deepClone();
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.typeReference != null)
            this.typeReference.setParent(this);
    }

    public SourceElement getFirstElement() {
        return getChildAt(0).getFirstElement();
    }

    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
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

    public void setTypeReference(TypeReference t) {
        this.typeReference = t;
    }

    public abstract List<? extends VariableSpecification> getVariables();

    public boolean isFinal() {
        return super.isFinal();
    }
}
