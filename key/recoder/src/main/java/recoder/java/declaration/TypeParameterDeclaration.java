package recoder.java.declaration;

import recoder.ModelException;
import recoder.abstraction.ClassType;
import recoder.abstraction.TypeParameter;
import recoder.convenience.Naming;
import recoder.java.Identifier;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.list.generic.ASTList;

public class TypeParameterDeclaration extends TypeDeclaration implements TypeReferenceContainer, TypeParameter {
    private static final long serialVersionUID = -6480521507901415027L;

    protected ASTList<TypeReference> bound;

    public TypeParameterDeclaration() {
    }

    public TypeParameterDeclaration(Identifier name, ASTList<TypeReference> bound) {
        super(name);
        this.bound = bound;
        makeParentRoleValid();
    }

    protected TypeParameterDeclaration(TypeParameterDeclaration proto) {
        super(proto);
        if (proto.bound != null)
            this.bound = proto.bound.deepClone();
        makeParentRoleValid();
    }

    public int getTypeReferenceCount() {
        return (this.bound == null) ? 0 : this.bound.size();
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (index == 0 && this.bound != null)
            return this.bound.get(index);
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public int getChildCount() {
        return ((this.name != null) ? 1 : 0) + ((this.bound != null) ? this.bound.size() : 0);
    }

    public ProgramElement getChildAt(int index) {
        if (this.name != null) {
            if (index == 0)
                return this.name;
            index--;
        }
        if (this.bound != null)
            return this.bound.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (child == this.name)
            return 0;
        int idx = this.bound.indexOf(child);
        if (idx != -1)
            return idx << 4 | 0x1;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (p == this.name) {
            this.name = (Identifier) q;
            if (this.name != null)
                this.name.setParent(this);
            return true;
        }
        if (this.bound != null) {
            int idx = this.bound.indexOf(p);
            if (idx != -1)
                if (q == null) {
                    this.bound.remove(idx);
                } else {
                    TypeReference tr = (TypeReference) q;
                    this.bound.set(idx, tr);
                    tr.setParent(this);
                }
            return true;
        }
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitTypeParameter(this);
    }

    public TypeParameterDeclaration deepClone() {
        return new TypeParameterDeclaration(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.bound != null)
            for (TypeReference tr : this.bound)
                tr.setParent(this);
    }

    public void validate() throws ModelException {
        if (this.members != null && this.members.size() != 0)
            throw new ModelException("No members allowed in TypeParameter");
    }

    public boolean isInterface() {
        return false;
    }

    public boolean isOrdinaryInterface() {
        return false;
    }

    public boolean isAnnotationType() {
        return false;
    }

    public boolean isEnumType() {
        return false;
    }

    public boolean isOrdinaryClass() {
        return false;
    }

    public ASTList<TypeParameterDeclaration> getTypeParameters() {
        return null;
    }

    public ASTList<TypeReference> getBounds() {
        return this.bound;
    }

    public String getParameterName() {
        return getName();
    }

    public int getBoundCount() {
        return (this.bound == null) ? 0 : this.bound.size();
    }

    public String getBoundName(int boundidx) {
        return Naming.toPathName(this.bound.get(boundidx));
    }

    public ASTList<TypeArgumentDeclaration> getBoundTypeArguments(int boundidx) {
        return this.bound.get(boundidx).getTypeArguments();
    }

    public boolean equals(Object o) {
        return TypeParameter.EqualsImplementor.equals(this, o);
    }

    public void setBound(ASTList<TypeReference> bound) {
        this.bound = bound;
    }

    public SourceElement getFirstElement() {
        return this.name;
    }

    public SourceElement getLastElement() {
        if (this.bound != null)
            return this.bound.get(this.bound.size() - 1);
        return this.name;
    }

    public ClassType getTypeInScope(String tname) {
        return null;
    }

    public void addTypeToScope(ClassType type, String tname) {
        throw new UnsupportedOperationException();
    }

    public void addVariableToScope(VariableSpecification var) {
        throw new UnsupportedOperationException();
    }

    public void removeTypeFromScope(String tname) {
        throw new UnsupportedOperationException();
    }

    public void removeVariableFromScope(String tname) {
        throw new UnsupportedOperationException();
    }
}
