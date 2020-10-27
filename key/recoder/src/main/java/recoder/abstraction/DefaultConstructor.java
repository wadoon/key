package recoder.abstraction;

import recoder.ModelException;
import recoder.convenience.Naming;
import recoder.service.ProgramModelInfo;
import recoder.util.Debug;

import java.util.List;

public class DefaultConstructor implements Constructor {
    protected ProgramModelInfo service;

    protected ClassType ownerClass;

    public DefaultConstructor(ClassType ownerClass) {
        Debug.assertNonnull(ownerClass);
        this.ownerClass = ownerClass;
    }

    public ProgramModelInfo getProgramModelInfo() {
        return this.service;
    }

    public void setProgramModelInfo(ProgramModelInfo service) {
        this.service = service;
    }

    public void validate() throws ModelException {
    }

    public boolean isFinal() {
        return false;
    }

    public boolean isStatic() {
        return true;
    }

    public boolean isPrivate() {
        return getContainingClassType().isEnumType();
    }

    public boolean isProtected() {
        return false;
    }

    public boolean isPublic() {
        return (getContainingClassType().isPublic() && !getContainingClassType().isEnumType());
    }

    public boolean isStrictFp() {
        return false;
    }

    public boolean isAbstract() {
        return false;
    }

    public boolean isNative() {
        return false;
    }

    public boolean isSynchronized() {
        return false;
    }

    public ClassType getContainingClassType() {
        return this.ownerClass;
    }

    public Type getReturnType() {
        return this.service.getReturnType(this);
    }

    public List<Type> getSignature() {
        return this.service.getSignature(this);
    }

    public List<ClassType> getExceptions() {
        return this.service.getExceptions(this);
    }

    public ClassTypeContainer getContainer() {
        return getContainingClassType();
    }

    public Package getPackage() {
        return this.service.getPackage(this);
    }

    public List<? extends ClassType> getTypes() {
        return this.service.getTypes(this);
    }

    public String getName() {
        return getContainingClassType().getName();
    }

    public String getFullName() {
        return Naming.getFullName(this);
    }

    public boolean isVarArgMethod() {
        return false;
    }

    public List<? extends AnnotationUse> getAnnotations() {
        return null;
    }

    public DefaultConstructor deepClone() {
        throw new UnsupportedOperationException("Cannot deep-clone default constructor");
    }

    public List<? extends TypeParameter> getTypeParameters() {
        return null;
    }
}
