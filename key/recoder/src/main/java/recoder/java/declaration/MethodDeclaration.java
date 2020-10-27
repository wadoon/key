package recoder.java.declaration;

import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.convenience.Naming;
import recoder.java.*;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.list.generic.ASTList;
import recoder.service.ProgramModelInfo;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.List;

public class MethodDeclaration extends JavaDeclaration implements MemberDeclaration, TypeReferenceContainer, NamedProgramElement, ParameterContainer, Method, VariableScope, TypeDeclarationContainer, TypeScope {
    private static final long serialVersionUID = -5270980702156620518L;

    protected TypeDeclaration parent;

    protected TypeReference returnType;

    protected Identifier name;

    protected ASTList<ParameterDeclaration> parameters;

    protected Throws exceptions;

    protected StatementBlock body;

    protected ProgramModelInfo service;

    protected ASTList<TypeParameterDeclaration> typeParameters;

    public MethodDeclaration() {
    }

    public MethodDeclaration(ASTList<DeclarationSpecifier> modifiers, TypeReference returnType, Identifier name, ASTList<ParameterDeclaration> parameters, Throws exceptions) {
        super(modifiers);
        setTypeReference(returnType);
        setIdentifier(name);
        setParameters(parameters);
        setThrown(exceptions);
        makeParentRoleValid();
    }

    public MethodDeclaration(ASTList<DeclarationSpecifier> modifiers, TypeReference returnType, Identifier name, ASTList<ParameterDeclaration> parameters, Throws exceptions, StatementBlock body) {
        super(modifiers);
        setTypeReference(returnType);
        setIdentifier(name);
        setParameters(parameters);
        setThrown(exceptions);
        setBody(body);
        makeParentRoleValid();
    }

    protected MethodDeclaration(MethodDeclaration proto) {
        super(proto);
        if (proto.returnType != null)
            this.returnType = proto.returnType.deepClone();
        if (proto.name != null)
            this.name = proto.name.deepClone();
        if (proto.parameters != null)
            this.parameters = proto.parameters.deepClone();
        if (proto.exceptions != null)
            this.exceptions = proto.exceptions.deepClone();
        if (proto.body != null)
            this.body = proto.body.deepClone();
        if (proto.typeParameters != null)
            this.typeParameters = proto.typeParameters.deepClone();
        makeParentRoleValid();
    }

    private static void updateModel() {
        factory.getServiceConfiguration().getChangeHistory().updateModel();
    }

    public MethodDeclaration deepClone() {
        return new MethodDeclaration(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.returnType != null)
            this.returnType.setParent(this);
        if (this.name != null)
            this.name.setParent(this);
        if (this.exceptions != null)
            this.exceptions.setParent(this);
        if (this.parameters != null)
            for (int i = this.parameters.size() - 1; i >= 0; i--)
                this.parameters.get(i).setParameterContainer(this);
        if (this.body != null)
            this.body.setStatementContainer(this);
        if (this.typeParameters != null)
            for (TypeParameterDeclaration tpd : this.typeParameters)
                tpd.setParent(this);
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.declarationSpecifiers != null) {
            int index = this.declarationSpecifiers.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x0;
        }
        if (this.returnType == child)
            return 1;
        if (this.name == child)
            return 2;
        if (this.parameters != null) {
            int index = this.parameters.indexOf(child);
            if (index >= 0)
                return index << 4 | 0x3;
        }
        if (this.exceptions == child)
            return 4;
        if (this.body == child)
            return 5;
        if (this.typeParameters != null) {
            int index = this.typeParameters.indexOf(child);
            if (index != -1)
                return index << 4 | 0x7;
        }
        return -1;
    }

    public SourceElement getFirstElement() {
        ProgramElement programElement = getChildAt(0);
        return (programElement instanceof TypeParameterDeclaration) ? this : programElement.getFirstElement();
    }

    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public TypeDeclaration getMemberParent() {
        return this.parent;
    }

    public void setMemberParent(TypeDeclaration decl) {
        this.parent = decl;
    }

    public int getChildCount() {
        int result = 0;
        if (this.declarationSpecifiers != null)
            result += this.declarationSpecifiers.size();
        if (this.returnType != null)
            result++;
        if (this.name != null)
            result++;
        if (this.parameters != null)
            result += this.parameters.size();
        if (this.exceptions != null)
            result++;
        if (this.body != null)
            result++;
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
        if (this.typeParameters != null) {
            int len = this.typeParameters.size();
            if (len > index)
                return this.typeParameters.get(index);
            index -= len;
        }
        if (this.returnType != null) {
            if (index == 0)
                return this.returnType;
            index--;
        }
        if (this.name != null) {
            if (index == 0)
                return this.name;
            index--;
        }
        if (this.parameters != null) {
            int len = this.parameters.size();
            if (len > index)
                return this.parameters.get(index);
            index -= len;
        }
        if (this.exceptions != null) {
            if (index == 0)
                return this.exceptions;
            index--;
        }
        if (this.body != null) {
            if (index == 0)
                return this.body;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getStatementCount() {
        return (this.body != null) ? 1 : 0;
    }

    public Statement getStatementAt(int index) {
        if (this.body != null && index == 0)
            return this.body;
        throw new ArrayIndexOutOfBoundsException();
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
        if (this.returnType == p) {
            TypeReference r = (TypeReference) q;
            this.returnType = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        if (this.name == p) {
            Identifier r = (Identifier) q;
            this.name = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        count = (this.parameters == null) ? 0 : this.parameters.size();
        for (i = 0; i < count; i++) {
            if (this.parameters.get(i) == p) {
                if (q == null) {
                    this.parameters.remove(i);
                } else {
                    ParameterDeclaration r = (ParameterDeclaration) q;
                    this.parameters.set(i, r);
                    r.setParameterContainer(this);
                }
                return true;
            }
        }
        if (this.exceptions == p) {
            Throws r = (Throws) q;
            this.exceptions = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        if (this.body == p) {
            StatementBlock r = (StatementBlock) q;
            this.body = r;
            if (r != null)
                r.setStatementContainer(this);
            return true;
        }
        if (this.typeParameters != null) {
            i = this.typeParameters.indexOf(p);
            if (i != -1) {
                if (q == null) {
                    this.typeParameters.remove(i);
                } else {
                    this.typeParameters.set(i, q);
                    ((TypeParameterDeclaration) q).setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    public int getTypeReferenceCount() {
        return (this.returnType != null) ? 1 : 0;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (this.returnType != null && index == 0)
            return this.returnType;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getParameterDeclarationCount() {
        return (this.parameters != null) ? this.parameters.size() : 0;
    }

    public ParameterDeclaration getParameterDeclarationAt(int index) {
        if (this.parameters != null)
            return this.parameters.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public TypeReference getTypeReference() {
        return this.returnType;
    }

    public void setTypeReference(TypeReference type) {
        this.returnType = type;
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

    public ASTList<ParameterDeclaration> getParameters() {
        return this.parameters;
    }

    public void setParameters(ASTList<ParameterDeclaration> list) {
        this.parameters = list;
    }

    public Throws getThrown() {
        return this.exceptions;
    }

    public void setThrown(Throws exceptions) {
        this.exceptions = exceptions;
    }

    public StatementBlock getBody() {
        return this.body;
    }

    public void setBody(StatementBlock body) {
        this.body = body;
    }

    public boolean isFinal() {
        return super.isFinal();
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
        return super.isStatic();
    }

    public boolean isStrictFp() {
        return super.isStrictFp();
    }

    public boolean isAbstract() {
        return (getASTParent() instanceof InterfaceDeclaration || super.isAbstract());
    }

    public boolean isNative() {
        return super.isNative();
    }

    public boolean isSynchronized() {
        return super.isSynchronized();
    }

    public ProgramModelInfo getProgramModelInfo() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        return this.service;
    }

    public void setProgramModelInfo(ProgramModelInfo service) {
        this.service = service;
    }

    public ClassType getContainingClassType() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        return this.service.getContainingClassType(this);
    }

    public Type getReturnType() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        return this.service.getReturnType(this);
    }

    public List<Type> getSignature() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        return this.service.getSignature(this);
    }

    public List<ClassType> getExceptions() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        return this.service.getExceptions(this);
    }

    public ClassTypeContainer getContainer() {
        return getContainingClassType();
    }

    public Package getPackage() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        return this.service.getPackage(this);
    }

    public List<TypeDeclaration> getTypes() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        return (getBody() == null) ? new ArrayList<TypeDeclaration>(0) : getBody().getTypesInScope();
    }

    public String getFullName() {
        return Naming.getFullName(this);
    }

    public boolean isDefinedScope() {
        return true;
    }

    public void setDefinedScope(boolean defined) {
    }

    public List<VariableSpecification> getVariablesInScope() {
        if (this.parameters == null || this.parameters.isEmpty())
            return new ArrayList<VariableSpecification>(0);
        int s = this.parameters.size();
        List<VariableSpecification> res = new ArrayList<VariableSpecification>(s);
        for (int i = 0; i < s; i++)
            res.add(this.parameters.get(i).getVariableSpecification());
        return res;
    }

    public VariableSpecification getVariableInScope(String tname) {
        Debug.assertNonnull(tname);
        if (this.parameters == null)
            return null;
        for (int i = 0, s = this.parameters.size(); i < s; i++) {
            VariableSpecification res = this.parameters.get(i).getVariableSpecification();
            if (tname.equals(res.getName()))
                return res;
        }
        return null;
    }

    public void addVariableToScope(VariableSpecification var) {
        Debug.assertNonnull(var);
    }

    public void removeVariableFromScope(String tname) {
        Debug.assertNonnull(tname);
    }

    public void accept(SourceVisitor v) {
        v.visitMethodDeclaration(this);
    }

    public boolean isVarArgMethod() {
        if (this.parameters == null || this.parameters.size() == 0)
            return false;
        return this.parameters.get(this.parameters.size() - 1).isVarArg();
    }

    public ASTList<TypeParameterDeclaration> getTypeParameters() {
        return this.typeParameters;
    }

    public void setTypeParameters(ASTList<TypeParameterDeclaration> typeParameters) {
        this.typeParameters = typeParameters;
    }

    public int getTypeDeclarationCount() {
        return (this.typeParameters == null) ? 0 : this.typeParameters.size();
    }

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (this.typeParameters == null)
            throw new IndexOutOfBoundsException();
        return this.typeParameters.get(index);
    }

    public List<TypeDeclaration> getTypesInScope() {
        if (this.typeParameters == null || this.typeParameters.isEmpty())
            return new ArrayList<TypeDeclaration>(0);
        List<TypeDeclaration> ctl = new ArrayList<TypeDeclaration>(this.typeParameters.size());
        for (TypeParameterDeclaration t : this.typeParameters)
            ctl.add(t);
        return ctl;
    }

    public ClassType getTypeInScope(String typename) {
        if (this.typeParameters == null)
            return null;
        for (TypeParameterDeclaration tpd : this.typeParameters) {
            if (typename.equals(tpd.getName()))
                return tpd;
        }
        return null;
    }

    public void addTypeToScope(ClassType type, String name) {
    }

    public void removeTypeFromScope(String name) {
    }
}
