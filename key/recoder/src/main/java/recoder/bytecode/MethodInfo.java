package recoder.bytecode;

import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.convenience.Naming;

import java.util.List;

public class MethodInfo extends MemberInfo implements Method {
    protected String[] paramtypes;

    protected String returntype;

    protected String[] exceptions;

    protected AnnotationUseInfo[][] paramAnnotations;

    protected List<TypeArgumentInfo>[] paramTypeArgs;

    protected List<TypeParameterInfo> typeParms;

    public MethodInfo(int accessFlags, String returntype, String name, String[] paramtypes, String[] exceptions, ClassFile cf) {
        super(accessFlags, name, cf);
        if (returntype != null)
            this.returntype = returntype.intern();
        this.paramtypes = paramtypes;
        int i;
        for (i = 0; i < paramtypes.length; i++)
            paramtypes[i] = paramtypes[i].intern();
        this.exceptions = exceptions;
        if (exceptions != null)
            for (i = 0; i < exceptions.length; i++)
                exceptions[i] = exceptions[i].intern();
    }

    public final String[] getParameterTypeNames() {
        return this.paramtypes;
    }

    public final AnnotationUseInfo[] getAnnotationsForParam(int paramNum) {
        if (this.paramAnnotations == null)
            return null;
        return this.paramAnnotations[paramNum];
    }

    public final List<TypeArgumentInfo> getTypeArgumentsForParam(int paramNum) {
        if (this.paramTypeArgs == null)
            return null;
        return this.paramTypeArgs[paramNum];
    }

    public final List<TypeArgumentInfo> getTypeArgumentsForReturnType() {
        if (this.paramTypeArgs == null)
            return null;
        return this.paramTypeArgs[this.paramTypeArgs.length - 1];
    }

    public final String[] getExceptionsInfo() {
        return this.exceptions;
    }

    public final String getTypeName() {
        return this.returntype;
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

    public String getFullName() {
        return Naming.getFullName(this);
    }

    public boolean isVarArgMethod() {
        return ((this.accessFlags & 0x80) != 0);
    }

    public List<TypeParameterInfo> getTypeParameters() {
        return this.typeParms;
    }
}
