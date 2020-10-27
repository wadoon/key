package recoder.java.declaration;

import recoder.java.Identifier;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.list.generic.ASTList;

public class InterfaceDeclaration extends TypeDeclaration {
    private static final long serialVersionUID = -9140653869908200337L;

    protected Extends extending;

    protected ASTList<TypeParameterDeclaration> typeParameters;

    public InterfaceDeclaration() {
    }

    public InterfaceDeclaration(ASTList<DeclarationSpecifier> modifiers, Identifier name, Extends extended, ASTList<MemberDeclaration> members, ASTList<TypeParameterDeclaration> typeParameters) {
        super(modifiers, name);
        setExtendedTypes(extended);
        setMembers(members);
        setTypeParameters(typeParameters);
        makeParentRoleValid();
    }

    public InterfaceDeclaration(ASTList<DeclarationSpecifier> modifiers, Identifier name, Extends extended, ASTList<MemberDeclaration> members) {
        this(modifiers, name, extended, members, null);
    }

    protected InterfaceDeclaration(InterfaceDeclaration proto) {
        super(proto);
        if (proto.extending != null)
            this.extending = proto.extending.deepClone();
        if (proto.typeParameters != null)
            this.typeParameters = proto.typeParameters.deepClone();
        makeParentRoleValid();
    }

    public InterfaceDeclaration deepClone() {
        return new InterfaceDeclaration(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.extending != null)
            this.extending.setParent(this);
        if (this.typeParameters != null)
            for (TypeParameterDeclaration tp : this.typeParameters)
                tp.setParent(this);
    }

    public int getChildCount() {
        int result = 0;
        if (this.declarationSpecifiers != null)
            result += this.declarationSpecifiers.size();
        if (this.name != null)
            result++;
        if (this.extending != null)
            result++;
        if (this.members != null)
            result += this.members.size();
        if (this.typeParameters != null)
            result += this.typeParameters.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.declarationSpecifiers != null) {
            int len = this.declarationSpecifiers.size();
            if (len > index)
                return this.declarationSpecifiers.get(index);
            index -= len;
        }
        if (this.name != null) {
            if (index == 0)
                return this.name;
            index--;
        }
        if (this.typeParameters != null) {
            int len = this.typeParameters.size();
            if (len > index)
                return this.typeParameters.get(index);
            index -= len;
        }
        if (this.extending != null) {
            if (index == 0)
                return this.extending;
            index--;
        }
        if (this.members != null) {
            int len = this.members.size();
            if (len > index)
                return this.members.get(index);
            index -= len;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.declarationSpecifiers != null) {
            int index = this.declarationSpecifiers.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        if (this.name == child)
            return 1;
        if (this.extending == child)
            return 2;
        if (this.members != null) {
            int index = this.members.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x4;
        }
        if (this.typeParameters != null) {
            int index = this.typeParameters.size();
            if (index >= 0)
                return index << 4 | 0x5;
        }
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        int count = (this.declarationSpecifiers == null) ? 0 : this.declarationSpecifiers.size();
        int i;
        for (i = 0; i < count; i++) {
            if (this.declarationSpecifiers.get(i) == p) {
                if (q == null) {
                    this.declarationSpecifiers.remove(i);
                } else {
                    DeclarationSpecifier r = (DeclarationSpecifier) q;
                    this.declarationSpecifiers.set(i, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        if (this.name == p) {
            Identifier r = (Identifier) q;
            this.name = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        if (this.extending == p) {
            Extends r = (Extends) q;
            this.extending = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        count = (this.members == null) ? 0 : this.members.size();
        for (i = 0; i < count; i++) {
            if (this.members.get(i) == p) {
                if (q == null) {
                    this.members.remove(i);
                } else {
                    MemberDeclaration r = (MemberDeclaration) q;
                    this.members.set(i, r);
                    r.setMemberParent(this);
                }
                return true;
            }
        }
        if (this.typeParameters != null) {
            int idx = this.typeParameters.indexOf(p);
            if (idx != -1) {
                if (q == null) {
                    this.typeParameters.remove(idx);
                } else {
                    TypeParameterDeclaration r = (TypeParameterDeclaration) q;
                    this.typeParameters.set(idx, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    public Extends getExtendedTypes() {
        return this.extending;
    }

    public void setExtendedTypes(Extends spec) {
        this.extending = spec;
    }

    public boolean isAbstract() {
        return true;
    }

    public boolean isNative() {
        return false;
    }

    public boolean isProtected() {
        return false;
    }

    public boolean isPrivate() {
        return false;
    }

    public boolean isStrictFp() {
        return false;
    }

    public boolean isSynchronized() {
        return false;
    }

    public boolean isTransient() {
        return false;
    }

    public boolean isVolatile() {
        return false;
    }

    public boolean isInterface() {
        return true;
    }

    public boolean isOrdinaryInterface() {
        return true;
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

    public void accept(SourceVisitor v) {
        v.visitInterfaceDeclaration(this);
    }

    public ASTList<TypeParameterDeclaration> getTypeParameters() {
        return this.typeParameters;
    }

    public void setTypeParameters(ASTList<TypeParameterDeclaration> typeParameters) {
        this.typeParameters = typeParameters;
    }
}
