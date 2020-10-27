package recoder.java.declaration;

import recoder.java.*;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class FieldDeclaration extends VariableDeclaration implements MemberDeclaration {
    private static final long serialVersionUID = 2577966836277961911L;

    protected TypeDeclaration parent;

    protected ASTList<FieldSpecification> fieldSpecs;

    public FieldDeclaration() {
    }

    public FieldDeclaration(TypeReference typeRef, Identifier name) {
        setTypeReference(typeRef);
        ASTArrayList aSTArrayList = new ASTArrayList(1);
        aSTArrayList.add(getFactory().createFieldSpecification(name));
        setFieldSpecifications((ASTList<FieldSpecification>) aSTArrayList);
        makeParentRoleValid();
    }

    public FieldDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef, Identifier name, Expression init) {
        setDeclarationSpecifiers(mods);
        setTypeReference(typeRef);
        ASTArrayList aSTArrayList = new ASTArrayList(1);
        aSTArrayList.add(getFactory().createFieldSpecification(name, init));
        setFieldSpecifications((ASTList<FieldSpecification>) aSTArrayList);
        makeParentRoleValid();
    }

    public FieldDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef, ASTList<FieldSpecification> vars) {
        setDeclarationSpecifiers(mods);
        setTypeReference(typeRef);
        setFieldSpecifications(vars);
        makeParentRoleValid();
    }

    protected FieldDeclaration(FieldDeclaration proto) {
        super(proto);
        if (proto.fieldSpecs != null)
            this.fieldSpecs = proto.fieldSpecs.deepClone();
        makeParentRoleValid();
    }

    public FieldDeclaration deepClone() {
        return new FieldDeclaration(this);
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public TypeDeclaration getMemberParent() {
        return this.parent;
    }

    public void setMemberParent(TypeDeclaration p) {
        this.parent = p;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.fieldSpecs != null)
            for (int i = this.fieldSpecs.size() - 1; i >= 0; i--)
                this.fieldSpecs.get(i).setParent(this);
    }

    public ASTList<FieldSpecification> getFieldSpecifications() {
        return this.fieldSpecs;
    }

    public void setFieldSpecifications(ASTList<FieldSpecification> l) {
        this.fieldSpecs = l;
    }

    public List<FieldSpecification> getVariables() {
        return new ArrayList<FieldSpecification>(this.fieldSpecs);
    }

    public int getChildCount() {
        int result = 0;
        if (this.declarationSpecifiers != null)
            result += this.declarationSpecifiers.size();
        if (this.typeReference != null)
            result++;
        if (this.fieldSpecs != null)
            result += this.fieldSpecs.size();
        return result;
    }

    public ProgramElement getChildAt(int index) {
        if (this.declarationSpecifiers != null) {
            int len = this.declarationSpecifiers.size();
            if (len > index)
                return this.declarationSpecifiers.get(index);
            index -= len;
        }
        if (this.typeReference != null) {
            if (index == 0)
                return this.typeReference;
            index--;
        }
        if (this.fieldSpecs != null)
            return this.fieldSpecs.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.declarationSpecifiers != null) {
            int index = this.declarationSpecifiers.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        if (this.typeReference == child)
            return 1;
        if (this.fieldSpecs != null) {
            int index = this.fieldSpecs.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x2;
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
        if (this.typeReference == p) {
            TypeReference r = (TypeReference) q;
            this.typeReference = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        count = (this.fieldSpecs == null) ? 0 : this.fieldSpecs.size();
        for (i = 0; i < count; i++) {
            if (this.fieldSpecs.get(i) == p) {
                if (q == null) {
                    this.fieldSpecs.remove(i);
                } else {
                    FieldSpecification r = (FieldSpecification) q;
                    this.fieldSpecs.set(i, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    public boolean isFinal() {
        return (getASTParent() instanceof InterfaceDeclaration || super.isFinal());
    }

    public boolean isPrivate() {
        return super.isPrivate();
    }

    public boolean isProtected() {
        return super.isProtected();
    }

    public boolean isPublic() {
        return (getASTParent() instanceof InterfaceDeclaration || super.isPublic());
    }

    public boolean isStatic() {
        return (getASTParent() instanceof InterfaceDeclaration || super.isStatic());
    }

    public boolean isTransient() {
        return (!(getASTParent() instanceof InterfaceDeclaration) && super.isTransient());
    }

    public boolean isStrictFp() {
        return super.isStrictFp();
    }

    public void accept(SourceVisitor v) {
        v.visitFieldDeclaration(this);
    }
}
