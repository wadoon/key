package recoder.java.declaration;

import recoder.java.*;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class LocalVariableDeclaration extends VariableDeclaration implements LoopInitializer {
    private static final long serialVersionUID = -504401927803552291L;

    protected StatementContainer parent;

    protected ASTList<VariableSpecification> varSpecs;

    public LocalVariableDeclaration() {
    }

    public LocalVariableDeclaration(TypeReference typeRef, Identifier name) {
        setTypeReference(typeRef);
        ASTArrayList aSTArrayList = new ASTArrayList(1);
        aSTArrayList.add(getFactory().createVariableSpecification(name));
        setVariableSpecifications((ASTList<VariableSpecification>) aSTArrayList);
        makeParentRoleValid();
    }

    public LocalVariableDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef, ASTList<VariableSpecification> vars) {
        setDeclarationSpecifiers(mods);
        setTypeReference(typeRef);
        setVariableSpecifications(vars);
        makeParentRoleValid();
    }

    public LocalVariableDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef, Identifier name, Expression init) {
        setDeclarationSpecifiers(mods);
        setTypeReference(typeRef);
        ASTArrayList aSTArrayList = new ASTArrayList(1);
        aSTArrayList.add(getFactory().createVariableSpecification(name, init));
        setVariableSpecifications((ASTList<VariableSpecification>) aSTArrayList);
        makeParentRoleValid();
    }

    protected LocalVariableDeclaration(LocalVariableDeclaration proto) {
        super(proto);
        if (proto.varSpecs != null)
            this.varSpecs = proto.varSpecs.deepClone();
        makeParentRoleValid();
    }

    public LocalVariableDeclaration deepClone() {
        return new LocalVariableDeclaration(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.varSpecs != null)
            for (int i = this.varSpecs.size() - 1; i >= 0; i--)
                this.varSpecs.get(i).setParent(this);
    }

    public ASTList<VariableSpecification> getVariableSpecifications() {
        return this.varSpecs;
    }

    public void setVariableSpecifications(ASTList<VariableSpecification> l) {
        this.varSpecs = l;
    }

    public List<VariableSpecification> getVariables() {
        return new ArrayList<VariableSpecification>(this.varSpecs);
    }

    public int getChildCount() {
        int result = 0;
        if (this.declarationSpecifiers != null)
            result += this.declarationSpecifiers.size();
        if (this.typeReference != null)
            result++;
        if (this.varSpecs != null)
            result += this.varSpecs.size();
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
        if (this.varSpecs != null)
            return this.varSpecs.get(index);
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
        if (this.varSpecs != null) {
            int index = this.varSpecs.indexOf(child);
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
        count = (this.varSpecs == null) ? 0 : this.varSpecs.size();
        for (i = 0; i < count; i++) {
            if (this.varSpecs.get(i) == p) {
                if (q == null) {
                    this.varSpecs.remove(i);
                } else {
                    VariableSpecification r = (VariableSpecification) q;
                    this.varSpecs.set(i, r);
                    r.setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public StatementContainer getStatementContainer() {
        return this.parent;
    }

    public void setStatementContainer(StatementContainer c) {
        this.parent = c;
    }

    public boolean isPrivate() {
        return false;
    }

    public boolean isProtected() {
        return false;
    }

    public boolean isPublic() {
        return false;
    }

    public boolean isStatic() {
        return false;
    }

    public boolean isTransient() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitLocalVariableDeclaration(this);
    }
}
