package recoder.java.declaration;

import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.convenience.Naming;
import recoder.java.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.ProgramModelInfo;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public abstract class TypeDeclaration extends JavaDeclaration implements NamedProgramElement, MemberDeclaration, TypeDeclarationContainer, ClassType, VariableScope, TypeScope {
    protected static final Map UNDEFINED_SCOPE = new HashMap<Object, Object>(1);
    protected Identifier name;
    protected TypeDeclarationContainer parent;
    protected ASTList<MemberDeclaration> members;
    protected ProgramModelInfo service;
    protected Map<String, TypeDeclaration> name2type = UNDEFINED_SCOPE;

    protected Map<String, FieldSpecification> name2field = UNDEFINED_SCOPE;

    public TypeDeclaration(Identifier name) {
        setIdentifier(name);
    }

    public TypeDeclaration(ASTList<DeclarationSpecifier> mods, Identifier name) {
        super(mods);
        setIdentifier(name);
    }

    protected TypeDeclaration(TypeDeclaration proto) {
        super(proto);
        if (proto.name != null)
            this.name = proto.name.deepClone();
        if (proto.members != null)
            this.members = proto.members.deepClone();
    }

    public TypeDeclaration() {
    }

    private static void updateModel() {
        factory.getServiceConfiguration().getChangeHistory().updateModel();
    }

    public void makeParentRoleValid() {
        if (this.declarationSpecifiers != null)
            for (int i = this.declarationSpecifiers.size() - 1; i >= 0; i--)
                this.declarationSpecifiers.get(i).setParent(this);
        if (this.name != null)
            this.name.setParent(this);
        if (this.members != null)
            for (int i = this.members.size() - 1; i >= 0; i--)
                this.members.get(i).setMemberParent(this);
    }

    public SourceElement getFirstElement() {
        if (this.declarationSpecifiers != null && !this.declarationSpecifiers.isEmpty())
            return this.declarationSpecifiers.get(0);
        return this;
    }

    public SourceElement getLastElement() {
        return this;
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

    public TypeDeclarationContainer getParent() {
        return this.parent;
    }

    public void setParent(TypeDeclarationContainer p) {
        this.parent = p;
    }

    public TypeDeclaration getMemberParent() {
        if (this.parent instanceof TypeDeclaration)
            return (TypeDeclaration) this.parent;
        return null;
    }

    public void setMemberParent(TypeDeclaration p) {
        this.parent = p;
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public ASTList<MemberDeclaration> getMembers() {
        return this.members;
    }

    public void setMembers(ASTList<MemberDeclaration> list) {
        this.members = list;
    }

    public int getTypeDeclarationCount() {
        int count = 0;
        if (this.members != null)
            for (int i = this.members.size() - 1; i >= 0; i--) {
                if (this.members.get(i) instanceof TypeDeclaration)
                    count++;
            }
        if (getTypeParameters() != null)
            count += getTypeParameters().size();
        return count;
    }

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (this.members != null) {
            int s = this.members.size();
            for (int i = 0; i < s && index >= 0; i++) {
                MemberDeclaration md = this.members.get(i);
                if (md instanceof TypeDeclaration) {
                    if (index == 0)
                        return (TypeDeclaration) md;
                    index--;
                }
            }
        }
        if (getTypeParameters() != null)
            return getTypeParameters().get(index);
        throw new ArrayIndexOutOfBoundsException();
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
        return (getASTParent() instanceof InterfaceDeclaration || super.isStatic());
    }

    public boolean isStrictFp() {
        return super.isStrictFp();
    }

    public boolean isAbstract() {
        return super.isAbstract();
    }

    public ProgramModelInfo getProgramModelInfo() {
        return this.service;
    }

    public void setProgramModelInfo(ProgramModelInfo service) {
        this.service = service;
    }

    public String getFullName() {
        return Naming.getFullName(this);
    }

    public ClassTypeContainer getContainer() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (this.service == null)
            Debug.error("Service not defined in TypeDeclaration " + getName());
        return this.service.getClassTypeContainer(this);
    }

    public ClassType getContainingClassType() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (this.service == null)
            Debug.error("Service not defined in TypeDeclaration " + getName());
        ClassTypeContainer ctc = this.service.getClassTypeContainer(this);
        return (ctc instanceof ClassType) ? (ClassType) ctc : null;
    }

    public Package getPackage() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (this.service == null)
            Debug.error("Service not defined in TypeDeclaration " + getName());
        return this.service.getPackage(this);
    }

    public List<ClassType> getSupertypes() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (this.service == null)
            Debug.error("Service not defined in TypeDeclaration " + getName());
        return this.service.getSupertypes(this);
    }

    public List<ClassType> getAllSupertypes() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (this.service == null)
            Debug.error("Service not defined in TypeDeclaration " + getName());
        return this.service.getAllSupertypes(this);
    }

    public List<FieldSpecification> getFields() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (this.service == null)
            Debug.error("Service not defined in TypeDeclaration " + getName());
        List<FieldSpecification> fields = this.service.getFields(this);
        return fields;
    }

    public List<Field> getAllFields() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (this.service == null)
            Debug.error("Service not defined in TypeDeclaration " + getName());
        return this.service.getAllFields(this);
    }

    public List<Method> getMethods() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (this.service == null)
            Debug.error("Service not defined in TypeDeclaration " + getName());
        return this.service.getMethods(this);
    }

    public List<Method> getAllMethods() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (this.service == null)
            Debug.error("Service not defined in TypeDeclaration " + getName());
        return this.service.getAllMethods(this);
    }

    public List<? extends Constructor> getConstructors() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (this.service == null)
            Debug.error("Service not defined in TypeDeclaration " + getName());
        return this.service.getConstructors(this);
    }

    public List<TypeDeclaration> getTypes() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (this.service == null)
            Debug.error("Service not defined in TypeDeclaration " + getName());
        List<TypeDeclaration> types = this.service.getTypes(this);
        return types;
    }

    public List<ClassType> getAllTypes() {
        if (this.service == null) {
            Debug.log("Zero service while " + Debug.makeStackTrace());
            updateModel();
        }
        if (this.service == null)
            Debug.error("Service not defined in TypeDeclaration " + getName());
        return this.service.getAllTypes(this);
    }

    public boolean isDefinedScope() {
        return (this.name2type != UNDEFINED_SCOPE);
    }

    public void setDefinedScope(boolean defined) {
        if (!defined) {
            this.name2type = UNDEFINED_SCOPE;
            this.name2field = UNDEFINED_SCOPE;
        } else {
            this.name2type = null;
            this.name2field = null;
        }
    }

    public List<TypeDeclaration> getTypesInScope() {
        if (this.name2type == null || this.name2type.isEmpty())
            return new ArrayList<TypeDeclaration>(0);
        List<TypeDeclaration> res = new ArrayList<TypeDeclaration>();
        for (TypeDeclaration td : this.name2type.values())
            res.add(td);
        return res;
    }

    public ClassType getTypeInScope(String tname) {
        Debug.assertNonnull(tname);
        if (this.name2type == null)
            return null;
        return this.name2type.get(tname);
    }

    public void addTypeToScope(ClassType type, String tname) {
        Debug.assertNonnull(type, tname);
        if (this.name2type == null || this.name2type == UNDEFINED_SCOPE)
            this.name2type = new HashMap<String, TypeDeclaration>();
        this.name2type.put(tname, (TypeDeclaration) type);
    }

    public void removeTypeFromScope(String tname) {
        Debug.assertNonnull(tname);
        if (this.name2type == null || this.name2type == UNDEFINED_SCOPE)
            return;
        this.name2type.remove(tname);
    }

    public List<FieldSpecification> getFieldsInScope() {
        if (this.name2field == null || this.name2field.isEmpty())
            return (List<FieldSpecification>) new ASTArrayList(0);
        ASTArrayList aSTArrayList = new ASTArrayList();
        for (FieldSpecification fs : this.name2field.values())
            aSTArrayList.add(fs);
        return (List<FieldSpecification>) aSTArrayList;
    }

    public List<? extends VariableSpecification> getVariablesInScope() {
        return getFieldsInScope();
    }

    public VariableSpecification getVariableInScope(String tname) {
        Debug.assertNonnull(tname);
        if (this.name2field == null)
            return null;
        return this.name2field.get(tname);
    }

    public void addVariableToScope(VariableSpecification var) {
        Debug.assertBoolean((var instanceof FieldSpecification || (var instanceof EnumConstantSpecification && this instanceof EnumDeclaration)));
        if (this.name2field == null || this.name2field == UNDEFINED_SCOPE)
            this.name2field = new HashMap<String, FieldSpecification>();
        this.name2field.put(var.getName(), (FieldSpecification) var);
    }

    public void removeVariableFromScope(String tname) {
        Debug.assertNonnull(tname);
        if (this.name2field == null || this.name2field == UNDEFINED_SCOPE)
            return;
        this.name2field.remove(tname);
    }

    public String toString() {
        return getClass().getSimpleName() + " " + getFullName();
    }

    public abstract boolean isInterface();

    public abstract ASTList<TypeParameterDeclaration> getTypeParameters();

    public abstract TypeDeclaration deepClone();
}
