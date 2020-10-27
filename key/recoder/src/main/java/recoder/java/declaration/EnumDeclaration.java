package recoder.java.declaration;

import recoder.ModelException;
import recoder.java.Identifier;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.declaration.modifier.Abstract;
import recoder.java.declaration.modifier.Final;
import recoder.list.generic.ASTList;
import recoder.service.IllegalModifierException;

import java.util.ArrayList;
import java.util.List;

public class EnumDeclaration extends TypeDeclaration {
    private static final long serialVersionUID = -6436741776435910109L;

    protected Implements implementing;

    public EnumDeclaration() {
    }

    public EnumDeclaration(ASTList<DeclarationSpecifier> declSpecs, Identifier name, Implements implementing, ASTList<MemberDeclaration> members) {
        super(declSpecs, name);
        setMembers(members);
        this.implementing = implementing;
        makeParentRoleValid();
    }

    public EnumDeclaration(EnumDeclaration proto) {
        super(proto);
        this.members = proto.members.deepClone();
        this.implementing = proto.implementing.deepClone();
        makeParentRoleValid();
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
        return true;
    }

    public boolean isOrdinaryClass() {
        return false;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.implementing != null)
            this.implementing.setParent(this);
    }

    public int getChildPositionCode(ProgramElement child) {
        int idx = this.declarationSpecifiers.indexOf(child);
        if (idx != -1)
            return idx << 4 | 0x0;
        if (child == this.name)
            return 1;
        if (child == this.implementing)
            return 2;
        idx = this.members.indexOf(child);
        if (idx != -1)
            return idx << 4 | 0x3;
        return -1;
    }

    public int getChildCount() {
        int res = 0;
        if (this.declarationSpecifiers != null)
            res += this.declarationSpecifiers.size();
        if (this.name != null)
            res++;
        if (this.implementing != null)
            res++;
        if (this.members != null)
            res += this.members.size();
        return res;
    }

    public ProgramElement getChildAt(int index) {
        if (this.declarationSpecifiers != null) {
            if (index < this.declarationSpecifiers.size())
                return this.declarationSpecifiers.get(index);
            index -= this.declarationSpecifiers.size();
        }
        if (this.name != null) {
            if (index == 0)
                return this.name;
            index--;
        }
        if (this.implementing != null) {
            if (index == 0)
                return this.implementing;
            index--;
        }
        return this.members.get(index);
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.name == p) {
            this.name = (Identifier) q;
            if (this.name != null)
                this.name.setParent(this);
            return true;
        }
        if (this.implementing == p) {
            this.implementing = (Implements) q;
            if (this.implementing != null)
                this.implementing.setParent(this);
            return true;
        }
        if (this.declarationSpecifiers != null) {
            int idx = this.declarationSpecifiers.indexOf(p);
            if (idx != -1) {
                if (q != null) {
                    DeclarationSpecifier ds = (DeclarationSpecifier) q;
                    this.declarationSpecifiers.set(idx, ds);
                    ds.setParent(this);
                } else {
                    this.declarationSpecifiers.remove(idx);
                }
                return true;
            }
        }
        if (this.members != null) {
            int idx = this.members.indexOf(p);
            if (idx != -1) {
                if (q != null) {
                    MemberDeclaration md = (MemberDeclaration) q;
                    this.members.set(idx, md);
                    md.setMemberParent(this);
                } else {
                    this.members.remove(idx);
                }
                return true;
            }
        }
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitEnumDeclaration(this);
    }

    public EnumDeclaration deepClone() {
        return new EnumDeclaration(this);
    }

    public Implements getImplementedTypes() {
        return this.implementing;
    }

    public void setImplementedTypes(Implements implementing) {
        this.implementing = implementing;
    }

    public boolean isFinal() {
        boolean res = true;
        for (int i = 0; i < this.members.size(); i++) {
            MemberDeclaration m = this.members.get(i);
            if (m instanceof EnumConstantDeclaration && (
                    (EnumConstantDeclaration) m).getEnumConstantSpecification().getConstructorReference().getClassDeclaration() != null) {
                res = false;
                break;
            }
        }
        return res;
    }

    public boolean isAbstract() {
        return false;
    }

    public boolean isStatic() {
        return (getASTParent() instanceof TypeDeclaration || super.isStatic());
    }

    public void validate() throws ModelException {
        if (containsModifier(Abstract.class))
            throw new IllegalModifierException("Illegal abstract modifier in EnumDeclaration " + getFullName());
        if (containsModifier(Final.class))
            throw new IllegalModifierException("Illegal final modifier in EnumDeclaration " + getFullName());
    }

    public ASTList<TypeParameterDeclaration> getTypeParameters() {
        return null;
    }

    public List<EnumConstantDeclaration> getConstants() {
        if (this.members == null)
            return new ArrayList<EnumConstantDeclaration>(0);
        List<EnumConstantDeclaration> result = new ArrayList<EnumConstantDeclaration>();
        for (int i = 0; i < this.members.size(); i++) {
            MemberDeclaration m = this.members.get(i);
            if (m instanceof EnumConstantDeclaration)
                result.add((EnumConstantDeclaration) m);
        }
        return result;
    }

    public List<MemberDeclaration> getNonConstantMembers() {
        if (this.members == null)
            return new ArrayList<MemberDeclaration>(0);
        List<MemberDeclaration> result = new ArrayList<MemberDeclaration>();
        for (int i = 0; i < this.members.size(); i++) {
            MemberDeclaration m = this.members.get(i);
            if (!(m instanceof EnumConstantDeclaration))
                result.add(m);
        }
        return result;
    }
}
