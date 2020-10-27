package recoder.abstraction;

import recoder.ModelException;
import recoder.service.ProgramModelInfo;

import java.util.List;

public class ParameterizedType implements ClassType {
    private final ClassType genericType;

    private final List<? extends TypeArgument> typeArgs;

    public ParameterizedType(ClassType genericType, List<? extends TypeArgument> typeArgs) {
        if (genericType == null)
            throw new NullPointerException();
        if (typeArgs == null)
            throw new NullPointerException();
        this.genericType = genericType;
        this.typeArgs = typeArgs;
    }

    public ClassType getGenericType() {
        return this.genericType;
    }

    public List<? extends TypeArgument> getTypeArgs() {
        return this.typeArgs;
    }

    public String getFullName() {
        return this.genericType.getFullName();
    }

    public ProgramModelInfo getProgramModelInfo() {
        return this.genericType.getProgramModelInfo();
    }

    public void setProgramModelInfo(ProgramModelInfo pmi) {
        throw new UnsupportedOperationException(pmi.getClass().getName() + " should not be set for Parameterized Types!");
    }

    public String getName() {
        return this.genericType.getName();
    }

    public void validate() throws ModelException {
    }

    public List<? extends TypeParameter> getTypeParameters() {
        return this.genericType.getTypeParameters();
    }

    public boolean isInterface() {
        return this.genericType.isInterface();
    }

    public boolean isOrdinaryInterface() {
        return this.genericType.isOrdinaryInterface();
    }

    public boolean isAnnotationType() {
        return this.genericType.isAnnotationType();
    }

    public boolean isEnumType() {
        return this.genericType.isEnumType();
    }

    public boolean isOrdinaryClass() {
        return this.genericType.isOrdinaryClass();
    }

    public boolean isAbstract() {
        return this.genericType.isAbstract();
    }

    public List<ClassType> getSupertypes() {
        return this.genericType.getSupertypes();
    }

    public List<ClassType> getAllSupertypes() {
        return this.genericType.getAllSupertypes();
    }

    public List<? extends Field> getFields() {
        return this.genericType.getFields();
    }

    public List<Field> getAllFields() {
        return this.genericType.getAllFields();
    }

    public List<Method> getMethods() {
        return this.genericType.getMethods();
    }

    public List<Method> getAllMethods() {
        return this.genericType.getAllMethods();
    }

    public List<? extends Constructor> getConstructors() {
        return this.genericType.getConstructors();
    }

    public List<ClassType> getAllTypes() {
        return this.genericType.getAllTypes();
    }

    public boolean isFinal() {
        return this.genericType.isFinal();
    }

    public boolean isStatic() {
        return this.genericType.isStatic();
    }

    public boolean isPrivate() {
        return this.genericType.isPrivate();
    }

    public boolean isProtected() {
        return this.genericType.isProtected();
    }

    public boolean isPublic() {
        return this.genericType.isPublic();
    }

    public boolean isStrictFp() {
        return this.genericType.isStrictFp();
    }

    public ClassType getContainingClassType() {
        return this.genericType.getContainingClassType();
    }

    public List<? extends AnnotationUse> getAnnotations() {
        return this.genericType.getAnnotations();
    }

    public List<? extends ClassType> getTypes() {
        return this.genericType.getTypes();
    }

    public Package getPackage() {
        return this.genericType.getPackage();
    }

    public ClassTypeContainer getContainer() {
        return this.genericType.getContainer();
    }
}
