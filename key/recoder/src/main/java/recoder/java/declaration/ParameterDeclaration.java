package recoder.java.declaration;

import recoder.java.*;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

import java.util.ArrayList;
import java.util.List;

public class ParameterDeclaration extends VariableDeclaration {
    private static final long serialVersionUID = -7820198330917949601L;

    protected ParameterContainer parent;

    protected VariableSpecification varSpec;

    protected boolean varArgParameter;

    public ParameterDeclaration() {
    }

    public ParameterDeclaration(TypeReference typeRef, Identifier name) {
        setTypeReference(typeRef);
        setVariableSpecification(getFactory().createVariableSpecification(name));
        makeParentRoleValid();
    }

    public ParameterDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef, Identifier name) {
        setDeclarationSpecifiers(mods);
        setTypeReference(typeRef);
        setVariableSpecification(getFactory().createVariableSpecification(name));
        makeParentRoleValid();
    }

    protected ParameterDeclaration(ParameterDeclaration proto) {
        super(proto);
        this.varSpec = proto.varSpec.deepClone();
        makeParentRoleValid();
    }

    public ParameterDeclaration deepClone() {
        return new ParameterDeclaration(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.varSpec != null)
            this.varSpec.setParent(this);
    }

    public VariableSpecification getVariableSpecification() {
        return this.varSpec;
    }

    public void setVariableSpecification(VariableSpecification vs) {
        this.varSpec = vs;
    }

    public List<VariableSpecification> getVariables() {
        List<VariableSpecification> res = new ArrayList<VariableSpecification>(1);
        res.add(this.varSpec);
        return res;
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public int getChildCount() {
        int result = 0;
        if (this.declarationSpecifiers != null)
            result += this.declarationSpecifiers.size();
        if (this.typeReference != null)
            result++;
        if (this.varSpec != null)
            result++;
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
        if (this.varSpec != null &&
                index == 0)
            return this.varSpec;
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
        if (this.varSpec == child)
            return 2;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        int count = (this.declarationSpecifiers == null) ? 0 : this.declarationSpecifiers.size();
        for (int i = 0; i < count; i++) {
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
        if (this.varSpec == p) {
            VariableSpecification r = (VariableSpecification) q;
            this.varSpec = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        return false;
    }

    public ParameterContainer getParameterContainer() {
        return this.parent;
    }

    public void setParameterContainer(ParameterContainer c) {
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
        v.visitParameterDeclaration(this);
    }

    public boolean isVarArg() {
        return this.varArgParameter;
    }

    public void setVarArg(boolean varArg) {
        this.varArgParameter = varArg;
    }
}
