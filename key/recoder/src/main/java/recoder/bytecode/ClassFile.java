// This file is part of the RECODER library and protected by the LGPL.

package recoder.bytecode;

import recoder.abstraction.Package;
import recoder.abstraction.*;

import java.util.Collections;
import java.util.List;

public class ClassFile extends ByteCodeElement implements ClassType {

    boolean isInner;
    List<TypeArgumentInfo> superClassTypeArguments;
    List<TypeArgumentInfo>[] superInterfacesTypeArguments;
    String enclosingMethod = null;
    int version;
    private String location;
    private String fullName;
    private String physicalName;
    private String superName;
    private String[] interfaceNames;
    private List<FieldInfo> fields;
    private List<MethodInfo> methods;
    private List<ConstructorInfo> constructors;
    private List<AnnotationUseInfo> annotations;
    private List<TypeParameterInfo> typeParams;
    private String[] innerClasses;
    private ArrayType arrayType;
    private ErasedType erasedType = null;

    ClassFile() {
        super();
    }

    public ArrayType getArrayType() {
        return arrayType;
    }

    public ArrayType createArrayType() {
        if (arrayType == null)
            arrayType = new ArrayType(this, service.getServiceConfiguration().getImplicitElementInfo());
        return arrayType;
    }

    void setSuperName(String superName) {
        this.superName = superName;
        if (superName != null) {
            this.superName = superName.intern();
        }
    }

    public final String getTypeName() {
        return fullName;
    }

    public final String getSuperClassName() {
        return superName;
    }

    public final List<TypeArgumentInfo> getSuperClassTypeArguments() {
        return superClassTypeArguments;
    }

    public final String[] getInterfaceNames() {
        return interfaceNames;
    }

    void setInterfaceNames(String[] interfaceNames) {
        this.interfaceNames = interfaceNames;
        if (interfaceNames != null) {
            for (int i = 0; i < interfaceNames.length; i++) {
                interfaceNames[i] = interfaceNames[i].intern();
            }
        }
    }

    public final List<TypeArgumentInfo> getSuperInterfaceTypeArguments(int ifidx) {
        return superInterfacesTypeArguments == null ? null : superInterfacesTypeArguments[ifidx];
    }

    public final List<FieldInfo> getFieldInfos() {
        return fields;
    }

    public final List<MethodInfo> getMethodInfos() {
        return methods;
    }

    public final List<ConstructorInfo> getConstructorInfos() {
        return constructors;
    }

    public final String[] getInnerClassNames() {
        return innerClasses;
    }

    void setInnerClassNames(String[] innerClassNames) {
        this.innerClasses = innerClassNames;
        if (innerClasses != null) {
            for (int i = 0; i < innerClassNames.length; i++) {
                innerClassNames[i] = innerClassNames[i].intern();
            }
        }
    }

    public final String getFullName() {
        return fullName;
    }

    void setFullName(String fullName) {
        this.fullName = fullName.intern();
    }

    public String getBinaryName() {
        return physicalName;
    }

    /**
     * Deprecated as of 0.92. Use <code>getBinaryName()</code> instead.
     *
     * @return the physical (=binary) name of this ClassFile
     * @Deprecated.
     * @see getBinaryName
     */
    @Deprecated
    public final String getPhysicalName() {
        return physicalName;
    }

    void setPhysicalName(String phkName) {
        this.physicalName = phkName;
    }

    public final ClassTypeContainer getContainer() {
        return service.getClassTypeContainer(this);
    }

    public ClassFile getContainingClassType() {
        ClassTypeContainer ctc = service.getClassTypeContainer(this);
        return (ctc instanceof ClassFile) ? (ClassFile) ctc : null;
    }

    public final Package getPackage() {
        return service.getPackage(this);
    }

    public final boolean isInterface() {
        return (accessFlags & AccessFlags.INTERFACE) != 0;
    }

    public boolean isOrdinaryInterface() {
        return (accessFlags & AccessFlags.INTERFACE) != 0 &&
                (accessFlags & AccessFlags.ANNOTATION) == 0;
    }

    public boolean isAnnotationType() {
        return (accessFlags & AccessFlags.ANNOTATION) != 0;
    }

    public boolean isEnumType() {
        return (accessFlags & AccessFlags.ENUM) != 0;
    }

    public boolean isOrdinaryClass() {
        return (accessFlags & AccessFlags.INTERFACE) == 0 &&
                (accessFlags & AccessFlags.ENUM) == 0;
    }

    public final List<ClassType> getSupertypes() {
        return service.getSupertypes(this);
    }

    public final List<ClassType> getAllSupertypes() {
        return service.getAllSupertypes(this);
    }

    @SuppressWarnings("unchecked")
    public final List<FieldInfo> getFields() {
        return (List<FieldInfo>) service.getFields(this);
    }

    void setFields(List<FieldInfo> fields) {
        this.fields = Collections.unmodifiableList(fields);
    }

    public final List<Field> getAllFields() {
        return service.getAllFields(this);
    }

    public final List<Method> getMethods() {
        return service.getMethods(this);
    }

    void setMethods(List<MethodInfo> methods) {
        this.methods = Collections.unmodifiableList(methods);
    }

    public final List<Method> getAllMethods() {
        return service.getAllMethods(this);
    }

    public final List<? extends Constructor> getConstructors() {
        return service.getConstructors(this);
    }

    void setConstructors(List<ConstructorInfo> constructors) {
        this.constructors = Collections.unmodifiableList(constructors);
    }

    @SuppressWarnings("unchecked")
    public final List<ClassFile> getTypes() {
        return (List<ClassFile>) service.getTypes(this);
    }

    public final List<ClassType> getAllTypes() {
        return service.getAllTypes(this);
    }

    /**
     * @return a list of annotations
     */
    public List<AnnotationUseInfo> getAnnotations() {
        return annotations;
    }

    void setAnnotations(List<AnnotationUseInfo> annotations) {
        this.annotations = Collections.unmodifiableList(annotations);
    }

    public List<TypeParameterInfo> getTypeParameters() {
        return typeParams;
    }

    public void setTypeParameters(List<TypeParameterInfo> typeParams) {
        this.typeParams = typeParams;
    }

    public String getLocation() {
        return location;
    }

    void setLocation(String location) {
        this.location = location;
    }

    @Override
    public String toString() {
        return "ClassFile " + getFullName();
    }

    public String getFullSignature() {
        String res = getFullName();
        if (getTypeParameters() == null || getTypeParameters().size() == 0)
            return res;
        res += "<";
        String del = "";
        for (TypeParameterInfo ta : getTypeParameters()) {
            res = res + del + ta.getFullSignature();
            del = ",";
        }
        res = res + ">";
        return res;
    }

    public ErasedType getErasedType() {
        if (erasedType == null)
            erasedType = new ErasedType(this, service.getServiceConfiguration().getImplicitElementInfo());
        return erasedType;
    }

    public boolean isInner() {
        return isInner;
    }

    public ClassType getBaseClassType() {
        return this;
    }

    /**
     * NOT FOR PUBLIC USE, SUBJECT TO CHANGE / BE REMOVED !!
     */
    public String getEnclosingMethod() {
        return enclosingMethod;
    }

    @Override
    public ClassFile getGenericMember() {
        return this;
    }

    public int getVersion() {
        return version;
    }
}

