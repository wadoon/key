package recoder.bytecode;

import recoder.abstraction.Package;
import recoder.abstraction.*;

import java.util.List;

public class ClassFile extends ByteCodeElement implements ClassType {
    String location;

    String fullName;

    String physicalName;

    String superName;

    String[] interfaceNames;

    List<FieldInfo> fields;

    List<MethodInfo> methods;

    List<ConstructorInfo> constructors;

    List<AnnotationUseInfo> annotations;

    List<TypeParameterInfo> typeParams;

    String[] innerClasses;

    List<TypeArgumentInfo> superClassTypeArguments;

    List<TypeArgumentInfo>[] superInterfacesTypeArguments;

    void setSuperName(String superName) {
        this.superName = superName;
        if (superName != null)
            this.superName = superName.intern();
    }

    public final String getTypeName() {
        return this.fullName;
    }

    public final String getSuperClassName() {
        return this.superName;
    }

    public final List<TypeArgumentInfo> getSuperClassTypeArguments() {
        return this.superClassTypeArguments;
    }

    public final String[] getInterfaceNames() {
        return this.interfaceNames;
    }

    void setInterfaceNames(String[] interfaceNames) {
        this.interfaceNames = interfaceNames;
        if (interfaceNames != null)
            for (int i = 0; i < interfaceNames.length; i++)
                interfaceNames[i] = interfaceNames[i].intern();
    }

    public final List<TypeArgumentInfo> getSuperInterfaceTypeArguments(int ifidx) {
        return (this.superInterfacesTypeArguments == null) ? null : this.superInterfacesTypeArguments[ifidx];
    }

    public final List<FieldInfo> getFieldInfos() {
        return this.fields;
    }

    public final List<MethodInfo> getMethodInfos() {
        return this.methods;
    }

    public final List<ConstructorInfo> getConstructorInfos() {
        return this.constructors;
    }

    public final String[] getInnerClassNames() {
        return this.innerClasses;
    }

    void setInnerClassNames(String[] innerClassNames) {
        this.innerClasses = innerClassNames;
        if (this.innerClasses != null)
            for (int i = 0; i < innerClassNames.length; i++)
                innerClassNames[i] = innerClassNames[i].intern();
    }

    public final String getFullName() {
        return this.fullName;
    }

    void setFullName(String fullName) {
        this.fullName = fullName.intern();
    }

    public final String getPhysicalName() {
        return this.physicalName;
    }

    void setPhysicalName(String phkName) {
        this.physicalName = phkName;
    }

    public final ClassTypeContainer getContainer() {
        return this.service.getClassTypeContainer(this);
    }

    public ClassType getContainingClassType() {
        ClassTypeContainer ctc = this.service.getClassTypeContainer(this);
        return (ctc instanceof ClassType) ? (ClassType) ctc : null;
    }

    public final Package getPackage() {
        return this.service.getPackage(this);
    }

    public final boolean isInterface() {
        return ((this.accessFlags & 0x200) != 0);
    }

    public boolean isOrdinaryInterface() {
        return ((this.accessFlags & 0x200) != 0 && (this.accessFlags & 0x2000) == 0);
    }

    public boolean isAnnotationType() {
        return ((this.accessFlags & 0x2000) != 0);
    }

    public boolean isEnumType() {
        return ((this.accessFlags & 0x4000) != 0);
    }

    public boolean isOrdinaryClass() {
        return ((this.accessFlags & 0x200) == 0 && (this.accessFlags & 0x4000) == 0);
    }

    public final List<ClassType> getSupertypes() {
        return this.service.getSupertypes(this);
    }

    public final List<ClassType> getAllSupertypes() {
        return this.service.getAllSupertypes(this);
    }

    public final List<FieldInfo> getFields() {
        return this.service.getFields(this);
    }

    void setFields(List<FieldInfo> fields) {
        this.fields = fields;
    }

    public final List<Field> getAllFields() {
        return this.service.getAllFields(this);
    }

    public final List<Method> getMethods() {
        return this.service.getMethods(this);
    }

    void setMethods(List<MethodInfo> methods) {
        this.methods = methods;
    }

    public final List<Method> getAllMethods() {
        return this.service.getAllMethods(this);
    }

    public final List<? extends Constructor> getConstructors() {
        return this.service.getConstructors(this);
    }

    void setConstructors(List<ConstructorInfo> constructors) {
        this.constructors = constructors;
    }

    public final List<ClassFile> getTypes() {
        return this.service.getTypes(this);
    }

    public final List<ClassType> getAllTypes() {
        return this.service.getAllTypes(this);
    }

    public List<AnnotationUseInfo> getAnnotations() {
        return this.annotations;
    }

    void setAnnotations(List<AnnotationUseInfo> annotations) {
        this.annotations = annotations;
    }

    public List<TypeParameterInfo> getTypeParameters() {
        return this.typeParams;
    }

    public void setTypeParameters(List<TypeParameterInfo> typeParams) {
        this.typeParams = typeParams;
    }

    public String getLocation() {
        return this.location;
    }

    void setLocation(String location) {
        this.location = location;
    }

    public String toString() {
        return "ClassFile " + getFullName();
    }
}
