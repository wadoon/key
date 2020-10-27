package recoder.service;

import recoder.ServiceConfiguration;
import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.java.declaration.EnumDeclaration;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class DefaultImplicitElementInfo extends DefaultProgramModelInfo implements ImplicitElementInfo {
    private final Map<ClassType, DefaultConstructor> type2defaultConstructor = new HashMap<ClassType, DefaultConstructor>();

    private final Map<EnumDeclaration, List<ImplicitEnumMethod>> type2implicitEnumMethods = new HashMap<EnumDeclaration, List<ImplicitEnumMethod>>();

    private List<ClassType> enumValueOfExceptions;

    public DefaultImplicitElementInfo(ServiceConfiguration config) {
        super(config);
        this.enumValueOfExceptions = null;
    }

    public DefaultConstructor getDefaultConstructor(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        DefaultConstructor cons = this.type2defaultConstructor.get(ct);
        if (cons == null) {
            cons = new DefaultConstructor(ct);
            cons.setProgramModelInfo(this);
            this.type2defaultConstructor.put(ct, cons);
        }
        return cons;
    }

    public List<ImplicitEnumMethod> getImplicitEnumMethods(EnumDeclaration etd) {
        if (etd == null)
            throw new NullPointerException();
        updateModel();
        List<ImplicitEnumMethod> res = this.type2implicitEnumMethods.get(etd);
        if (res == null) {
            res = new ArrayList<ImplicitEnumMethod>(2);
            ImplicitEnumValueOf implicitEnumValueOf = new ImplicitEnumValueOf(etd);
            implicitEnumValueOf.setProgramModelInfo(this);
            res.add(implicitEnumValueOf);
            ImplicitEnumValues implicitEnumValues = new ImplicitEnumValues(etd);
            implicitEnumValues.setProgramModelInfo(this);
            res.add(implicitEnumValues);
            this.type2implicitEnumMethods.put(etd, res);
        }
        return res;
    }

    public Type getType(ProgramModelElement pme) {
        if (pme instanceof recoder.abstraction.NullType || pme instanceof recoder.abstraction.ArrayType || pme instanceof IntersectionType)
            return (Type) pme;
        if (pme instanceof Package)
            return null;
        return getReturnType((Method) pme);
    }

    public Package getPackage(ProgramModelElement pme) {
        if (pme instanceof Package)
            return (Package) pme;
        if (pme instanceof DefaultConstructor || pme instanceof ImplicitEnumMethod) {
            updateModel();
            return getContainingClassType((Member) pme).getPackage();
        }
        return null;
    }

    public List<? extends ClassType> getTypes(ClassTypeContainer ctc) {
        if (ctc instanceof Package)
            return this.serviceConfiguration.getNameInfo().getTypes((Package) ctc);
        if (ctc instanceof DefaultConstructor)
            return new ArrayList<ClassType>(0);
        return null;
    }

    public List<ClassType> getAllTypes(ClassType ct) {
        assert ct == getNameInfo().getNullType();
        return null;
    }

    public ClassTypeContainer getClassTypeContainer(ClassType ct) {
        assert ct == getNameInfo().getNullType();
        return null;
    }

    public List<ClassType> getSupertypes(ClassType ct) {
        if (ct instanceof IntersectionType)
            return ct.getSupertypes();
        return null;
    }

    public List<ClassType> getAllSupertypes(ClassType ct) {
        if (ct instanceof recoder.abstraction.NullType) {
            List<ClassType> result = new ArrayList<ClassType>(1);
            result.add(ct);
            return result;
        }
        if (ct instanceof IntersectionType)
            return getAllSubtypes(ct);
        return null;
    }

    public List<? extends Field> getFields(ClassType ct) {
        assert ct == getNameInfo().getNullType();
        return null;
    }

    public List<Field> getAllFields(ClassType ct) {
        if (ct instanceof IntersectionType)
            return super.getAllFields(ct);
        return null;
    }

    public List<Method> getMethods(ClassType ct) {
        assert ct == getNameInfo().getNullType();
        return null;
    }

    public List<Method> getAllMethods(ClassType ct) {
        if (ct instanceof IntersectionType)
            return super.getAllMethods(ct);
        return null;
    }

    public List<Constructor> getConstructors(ClassType ct) {
        assert ct == getNameInfo().getNullType();
        return null;
    }

    public boolean isInterface(ClassType ct) {
        assert ct == getNameInfo().getNullType();
        return false;
    }

    public ClassType getContainingClassType(Member m) {
        if (m instanceof DefaultConstructor || m instanceof ImplicitEnumMethod)
            return m.getContainingClassType();
        return null;
    }

    public List<Type> getSignature(Method m) {
        if (m instanceof ImplicitEnumValueOf) {
            ArrayList<Type> tal = new ArrayList<Type>(1);
            tal.add(getServiceConfiguration().getNameInfo().getJavaLangString());
            return tal;
        }
        return new ArrayList<Type>(0);
    }

    public List<ClassType> getExceptions(Method m) {
        if (m instanceof ImplicitEnumValueOf) {
            if (this.enumValueOfExceptions == null) {
                this.enumValueOfExceptions = new ArrayList<ClassType>(2);
                this.enumValueOfExceptions.add(getNameInfo().getClassType("java.lang.IllegalArgumentException"));
                this.enumValueOfExceptions.add(getNameInfo().getClassType("java.lang.NullPointerException"));
            }
            return this.enumValueOfExceptions;
        }
        return new ArrayList<ClassType>(0);
    }

    public Type getReturnType(Method m) {
        if (m instanceof ImplicitEnumValueOf)
            return m.getContainingClassType();
        if (m instanceof ImplicitEnumValues)
            return getServiceConfiguration().getNameInfo().createArrayType(m.getContainingClassType());
        return null;
    }
}
