package recoder.bytecode;

import recoder.ModelException;
import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.convenience.Naming;
import recoder.service.ProgramModelInfo;

import java.util.List;

public class TypeParameterInfo implements TypeParameter, ClassType {
    protected String name;

    protected String[] boundNames;

    protected List<TypeArgumentInfo>[] boundArgs;

    protected ClassFile containingClassFile;

    public TypeParameterInfo(String name, String[] boundNames, List<TypeArgumentInfo>[] boundArgs, ClassFile containingClassFile) {
        this.name = name;
        this.boundNames = boundNames;
        this.boundArgs = boundArgs;
        this.containingClassFile = containingClassFile;
    }

    public String getFullName() {
        return Naming.dot(this.containingClassFile.fullName, this.name);
    }

    public ProgramModelInfo getProgramModelInfo() {
        return this.containingClassFile.getProgramModelInfo();
    }

    public void setProgramModelInfo(ProgramModelInfo pmi) {
        throw new UnsupportedOperationException(pmi.getClass().getName() + " should not be set for TypeParamterInfo");
    }

    public String getName() {
        return this.name;
    }

    public void validate() throws ModelException {
    }

    public String getParameterName() {
        return this.name;
    }

    public int getBoundCount() {
        return this.boundNames.length;
    }

    public String getBoundName(int boundidx) {
        return this.boundNames[boundidx];
    }

    public List<TypeArgumentInfo> getBoundTypeArguments(int boundidx) {
        return this.boundArgs[boundidx];
    }

    public boolean equals(Object o) {
        return TypeParameter.EqualsImplementor.equals(this, o);
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

    public boolean isAbstract() {
        return false;
    }

    public List<ClassType> getSupertypes() {
        return this.containingClassFile.getProgramModelInfo().getSupertypes(this);
    }

    public List<ClassType> getAllSupertypes() {
        return this.containingClassFile.getProgramModelInfo().getAllSupertypes(this);
    }

    public List<FieldInfo> getFields() {
        return null;
    }

    public List<Field> getAllFields() {
        return null;
    }

    public List<Method> getMethods() {
        return null;
    }

    public List<Method> getAllMethods() {
        return this.containingClassFile.getProgramModelInfo().getAllMethods(this);
    }

    public List<Constructor> getConstructors() {
        return null;
    }

    public List<ClassType> getAllTypes() {
        return null;
    }

    public List<? extends TypeParameter> getTypeParameters() {
        return null;
    }

    public boolean isFinal() {
        return false;
    }

    public boolean isStatic() {
        return false;
    }

    public boolean isPrivate() {
        return false;
    }

    public boolean isProtected() {
        return false;
    }

    public boolean isPublic() {
        return true;
    }

    public boolean isStrictFp() {
        return false;
    }

    public ClassType getContainingClassType() {
        return this.containingClassFile;
    }

    public List<? extends AnnotationUse> getAnnotations() {
        return null;
    }

    public List<ClassType> getTypes() {
        return null;
    }

    public Package getPackage() {
        return this.containingClassFile.getPackage();
    }

    public ClassTypeContainer getContainer() {
        return this.containingClassFile;
    }
}
