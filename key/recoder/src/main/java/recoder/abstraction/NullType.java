package recoder.abstraction;

import recoder.service.ProgramModelInfo;

import java.util.List;

public class NullType implements ClassType {
    public static final String NULL = "null";

    private ProgramModelInfo pmi;

    public NullType(ProgramModelInfo info) {
        this.pmi = info;
    }

    public String getName() {
        return "null";
    }

    public String getFullName() {
        return "null";
    }

    public ProgramModelInfo getProgramModelInfo() {
        return this.pmi;
    }

    public void setProgramModelInfo(ProgramModelInfo info) {
        this.pmi = info;
    }

    public void validate() {
    }

    public boolean isFinal() {
        return true;
    }

    public boolean isStatic() {
        return true;
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

    public List<? extends ClassType> getTypes() {
        return this.pmi.getTypes(this);
    }

    public List<ClassType> getAllTypes() {
        return this.pmi.getAllTypes(this);
    }

    public ClassType getContainingClassType() {
        return this.pmi.getContainingClassType(this);
    }

    public ClassTypeContainer getContainer() {
        return this.pmi.getClassTypeContainer(this);
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
        return true;
    }

    public boolean isAbstract() {
        return false;
    }

    public List<ClassType> getSupertypes() {
        return this.pmi.getSupertypes(this);
    }

    public List<ClassType> getAllSupertypes() {
        return this.pmi.getAllSupertypes(this);
    }

    public List<? extends Field> getFields() {
        return this.pmi.getFields(this);
    }

    public List<Field> getAllFields() {
        return this.pmi.getAllFields(this);
    }

    public List<Method> getMethods() {
        return this.pmi.getMethods(this);
    }

    public List<? extends Constructor> getConstructors() {
        return this.pmi.getConstructors(this);
    }

    public List<Method> getAllMethods() {
        return this.pmi.getAllMethods(this);
    }

    public Package getPackage() {
        return this.pmi.getPackage(this);
    }

    public List<? extends AnnotationUse> getAnnotations() {
        return null;
    }

    public List<? extends TypeParameter> getTypeParameters() {
        return null;
    }
}
