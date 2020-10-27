package recoder.abstraction;

import recoder.ModelException;
import recoder.convenience.Naming;
import recoder.service.ProgramModelInfo;

import java.util.List;

public abstract class ImplicitEnumMethod implements Method {
    protected ProgramModelInfo service;

    protected ClassType ownerClass;

    protected String name;

    public ImplicitEnumMethod(ClassType ownerClass) {
        if (ownerClass == null)
            throw new NullPointerException();
        this.ownerClass = ownerClass;
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

    public boolean isVarArgMethod() {
        return false;
    }

    public boolean isFinal() {
        return false;
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

    public ClassType getContainingClassType() {
        return this.ownerClass;
    }

    public List<? extends AnnotationUse> getAnnotations() {
        return null;
    }

    public String getFullName() {
        return Naming.getFullName(this);
    }

    public ProgramModelInfo getProgramModelInfo() {
        return this.service;
    }

    public void setProgramModelInfo(ProgramModelInfo pmi) {
        this.service = pmi;
    }

    public void validate() throws ModelException {
    }

    public List<ClassType> getTypes() {
        return null;
    }

    public Package getPackage() {
        return this.service.getPackage(this);
    }

    public ClassTypeContainer getContainer() {
        return getContainingClassType();
    }

    public List<ClassType> getExceptions() {
        return this.service.getExceptions(this);
    }

    public Type getReturnType() {
        return this.service.getReturnType(this);
    }

    public List<Type> getSignature() {
        return this.service.getSignature(this);
    }
}
