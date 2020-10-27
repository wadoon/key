package recoder.java.declaration;

import recoder.java.*;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public abstract class InheritanceSpecification extends JavaNonTerminalProgramElement implements TypeReferenceContainer {
    protected TypeDeclaration parent;

    protected ASTList<TypeReference> supertypes;

    public InheritanceSpecification() {
    }

    public InheritanceSpecification(TypeReference supertype) {
        this.supertypes = (ASTList<TypeReference>) new ASTArrayList(1);
        this.supertypes.add(supertype);
    }

    public InheritanceSpecification(ASTList<TypeReference> supertypes) {
        this.supertypes = supertypes;
    }

    protected InheritanceSpecification(InheritanceSpecification proto) {
        super(proto);
        if (proto.supertypes != null)
            this.supertypes = proto.supertypes.deepClone();
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.supertypes != null)
            for (int i = this.supertypes.size() - 1; i >= 0; i--)
                this.supertypes.get(i).setParent(this);
    }

    public SourceElement getLastElement() {
        if (this.supertypes == null)
            return this;
        return this.supertypes.get(this.supertypes.size() - 1);
    }

    public int getChildCount() {
        int result = 0;
        if (this.supertypes != null)
            result += this.supertypes.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.supertypes != null)
            return this.supertypes.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.supertypes != null) {
            int index = this.supertypes.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        int count = (this.supertypes == null) ? 0 : this.supertypes.size();
        for (int i = 0; i < count; i++) {
            if (this.supertypes.get(i) == p) {
                if (q == null) {
                    this.supertypes.remove(i);
                } else {
                    TypeReference r = (TypeReference) q;
                    this.supertypes.set(i, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    public TypeDeclaration getParent() {
        return this.parent;
    }

    public void setParent(TypeDeclaration decl) {
        this.parent = decl;
    }

    public ASTList<TypeReference> getSupertypes() {
        return this.supertypes;
    }

    public void setSupertypes(ASTList<TypeReference> list) {
        this.supertypes = list;
    }

    public int getTypeReferenceCount() {
        return (this.supertypes != null) ? this.supertypes.size() : 0;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (this.supertypes != null)
            return this.supertypes.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }
}
