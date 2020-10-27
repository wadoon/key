package recoder.service;

import recoder.ModelElement;
import recoder.ServiceConfiguration;
import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.bytecode.*;
import recoder.convenience.Format;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class DefaultByteCodeInfo extends DefaultProgramModelInfo implements ByteCodeInfo {
    private final Map<ProgramModelElement, ClassTypeContainer> element2container = new HashMap<ProgramModelElement, ClassTypeContainer>(256);
    private final Map<ClassTypeContainer, List<ClassType>> containedTypes = new HashMap<ClassTypeContainer, List<ClassType>>(32);
    private final Map<Method, List<Type>> method2signature = new HashMap<Method, List<Type>>(128);

    public DefaultByteCodeInfo(ServiceConfiguration config) {
        super(config);
    }

    private ByteCodeElement getByteCodeElement(ProgramModelElement pme) {
        if (pme instanceof ByteCodeElement)
            return (ByteCodeElement) pme;
        return null;
    }

    public final ClassFile getClassFile(ClassType ct) {
        return (ClassFile) getByteCodeElement(ct);
    }

    public final MethodInfo getMethodInfo(Method m) {
        return (MethodInfo) getByteCodeElement(m);
    }

    public final ConstructorInfo getConstructorInfo(Constructor c) {
        return (ConstructorInfo) getByteCodeElement(c);
    }

    public final FieldInfo getFieldInfo(Field f) {
        return (FieldInfo) getByteCodeElement(f);
    }

    public Type getType(ByteCodeElement bce) {
        TypeParameter typeParameter;
        Type type1;
        ParameterizedType parameterizedType;
        Type result = null;
        String typeName = bce.getTypeName();
        if (bce instanceof MethodInfo) {
            MethodInfo mi = (MethodInfo) bce;
            List<? extends TypeParameter> tpl = mi.getContainingClassType().getTypeParameters();
            for (TypeParameter tp : tpl) {
                if (typeName.equals(tp.getName()))
                    typeParameter = tp;
            }
        }
        if (typeParameter == null)
            type1 = getNameInfo().getType(typeName);
        if (bce instanceof MethodInfo) {
            MethodInfo mi = (MethodInfo) bce;
            List<TypeArgumentInfo> typeArgs = mi.getTypeArgumentsForReturnType();
            if (typeArgs != null && typeArgs.size() != 0)
                if (type1 instanceof ArrayType) {
                    type1 = makeParameterizedArrayType(type1, typeArgs);
                } else {
                    parameterizedType = new ParameterizedType((ClassType) type1, typeArgs);
                }
        }
        return parameterizedType;
    }

    public Type getType(ProgramModelElement pme) {
        Debug.assertNonnull(pme);
        Type result = null;
        if (pme instanceof Type) {
            result = (Type) pme;
        } else {
            ByteCodeElement bci = getByteCodeElement(pme);
            if (bci == null) {
                result = pme.getProgramModelInfo().getType(pme);
            } else {
                result = getType(bci);
            }
        }
        return result;
    }

    public Package getPackage(ProgramModelElement pme) {
        Debug.assertNonnull(pme);
        ProgramModelElement x = this.element2container.get(pme);
        while (x != null && !(x instanceof Package))
            x = this.element2container.get(x);
        return (Package) x;
    }

    public List<? extends ClassType> getTypes(ClassTypeContainer ctc) {
        Debug.assertNonnull(ctc);
        if (ctc instanceof ByteCodeElement) {
            List<ClassType> ctl = this.containedTypes.get(ctc);
            return (ctl == null) ? new ArrayList<ClassType>(0) : ctl;
        }
        return ctc.getProgramModelInfo().getTypes(ctc);
    }

    public ClassTypeContainer getClassTypeContainer(ClassType ct) {
        return this.element2container.get(ct);
    }

    public List<ClassType> getSupertypes(ClassType ct) {
        Debug.assertNonnull(ct);
        if (ct instanceof TypeParameterInfo) {
            TypeParameterInfo tp = (TypeParameterInfo) ct;
            List<ClassType> res = new ArrayList<ClassType>();
            if (tp.getBoundCount() == 0) {
                res.add(getNameInfo().getJavaLangObject());
            } else {
                for (int i = 0; i < tp.getBoundCount(); i++)
                    res.add(getNameInfo().getClassType(tp.getBoundName(i)));
            }
            return res;
        }
        ClassFile cf = getClassFile(ct);
        if (cf == null)
            return ct.getProgramModelInfo().getSupertypes(ct);
        ClassFileCacheEntry cfce = (ClassFileCacheEntry) this.classTypeCache.get(ct);
        Debug.assertNonnull(cfce);
        Debug.assertNonnull(cfce.supertypes);
        return cfce.supertypes;
    }

    public List<? extends Field> getFields(ClassType ct) {
        Debug.assertNonnull(ct);
        if (ct instanceof ClassFile)
            return ((ClassFile) ct).getFieldInfos();
        return ct.getProgramModelInfo().getFields(ct);
    }

    public List<Method> getMethods(ClassType ct) {
        Debug.assertNonnull(ct);
        if (ct instanceof ClassFile)
            return new ArrayList<Method>(((ClassFile) ct).getMethodInfos());
        return ct.getProgramModelInfo().getMethods(ct);
    }

    public List<? extends Constructor> getConstructors(ClassType ct) {
        Debug.assertNonnull(ct);
        if (ct instanceof ClassFile)
            return ((ClassFile) ct).getConstructorInfos();
        return ct.getProgramModelInfo().getConstructors(ct);
    }

    public ClassType getContainingClassType(Member m) {
        return (ClassType) this.element2container.get(m);
    }

    public List<Type> getSignature(Method m) {
        List<Type> result;
        Debug.assertNonnull(m);
        MethodInfo mi = getMethodInfo(m);
        if (mi == null) {
            result = m.getProgramModelInfo().getSignature(m);
        } else {
            String[] ptypes = mi.getParameterTypeNames();
            int pcount = ptypes.length;
            if (pcount == 0) {
                result = new ArrayList<Type>(0);
            } else {
                result = this.method2signature.get(m);
                if (result == null) {
                    NameInfo ni = getNameInfo();
                    List<Type> res = new ArrayList<Type>(pcount);
                    for (int i = 0; i < pcount; i++) {
                        ArrayType arrayType;
                        Type type1;
                        ParameterizedType parameterizedType;
                        Type t = null;
                        String basename = ptypes[i];
                        int dim;
                        if ((dim = basename.indexOf('[')) != -1)
                            basename = basename.substring(0, dim);
                        boolean checkClassTypeParameters = true;
                        List<? extends TypeParameter> tpl = mi.getTypeParameters();
                        if (tpl != null)
                            for (TypeParameter tp : tpl) {
                                if (basename.equals(tp.getName())) {
                                    TypeParameter typeParameter = tp;
                                    if (dim != -1) {
                                        dim = (ptypes[i].length() - dim) / 2;
                                        while (dim != 0) {
                                            arrayType = ni.createArrayType(tp);
                                            dim--;
                                        }
                                    }
                                    checkClassTypeParameters = false;
                                    break;
                                }
                            }
                        if (checkClassTypeParameters) {
                            tpl = mi.getContainingClassType().getTypeParameters();
                            for (TypeParameter tp : tpl) {
                                if (basename.equals(tp.getName())) {
                                    TypeParameter typeParameter = tp;
                                    if (dim != -1) {
                                        dim = (ptypes[i].length() - dim) / 2;
                                        while (dim != 0) {
                                            arrayType = ni.createArrayType(tp);
                                            dim--;
                                        }
                                    }
                                    break;
                                }
                            }
                        }
                        if (arrayType == null)
                            type1 = ni.getType(ptypes[i]);
                        if (mi.getTypeArgumentsForParam(i) != null)
                            if (type1 instanceof ArrayType) {
                                type1 = makeParameterizedArrayType(type1, mi.getTypeArgumentsForParam(i));
                            } else {
                                parameterizedType = new ParameterizedType((ClassType) type1, mi.getTypeArgumentsForParam(i));
                            }
                        res.add(parameterizedType);
                    }
                    result = res;
                    this.method2signature.put(m, result);
                }
            }
        }
        return result;
    }

    public List<ClassType> getExceptions(Method m) {
        Debug.assertNonnull(m);
        MethodInfo mi = getMethodInfo(m);
        if (mi == null)
            return m.getProgramModelInfo().getExceptions(m);
        String[] etypes = mi.getExceptionsInfo();
        if (etypes == null || etypes.length == 0)
            return new ArrayList<ClassType>(0);
        List<ClassType> res = new ArrayList<ClassType>(etypes.length);
        NameInfo ni = getNameInfo();
        for (int i = 0; i < etypes.length; i++)
            res.add(ni.getClassType(etypes[i]));
        return res;
    }

    public Type getReturnType(Method m) {
        return getType(m);
    }

    public void register(ClassFile cf) {
        Package package_;
        Debug.assertNonnull(cf);
        ClassFileCacheEntry cfce = (ClassFileCacheEntry) this.classTypeCache.get(cf);
        if (cfce != null)
            return;
        if (cf.getName().equals("package-info"))
            return;
        cfce = new ClassFileCacheEntry();
        this.classTypeCache.put(cf, cfce);
        String classname = cf.getPhysicalName();
        NameInfo ni = getNameInfo();
        cf.setProgramModelInfo(this);
        ni.register(cf);
        int ldp = classname.lastIndexOf('$');
        if (ldp >= 0) {
            String outerClassName = classname.substring(0, ldp);
            classname = classname.substring(ldp + 1);
            ClassType outerClass = ni.getClassType(outerClassName.replace('$', '.'));
            if (outerClass == null)
                do {
                    ldp = outerClassName.lastIndexOf('$');
                    if (ldp < 0)
                        continue;
                    outerClassName = outerClassName.substring(0, ldp);
                    if (outerClassName.length() <= 0)
                        continue;
                    outerClass = ni.getClassType(outerClassName.replace('$', '.'));
                } while (ldp >= 0 && outerClass == null);
            if (outerClass instanceof ClassFile) {
                register((ClassFile) outerClass);
            } else {
                Debug.log("Found a non-ClassFile outer class of " + classname + ":" + Format.toString("%c %N", outerClass));
            }
            ClassType classType1 = outerClass;
        } else {
            ldp = classname.lastIndexOf('.');
            String packageName = "";
            if (ldp != -1)
                packageName = classname.substring(0, ldp);
            package_ = ni.createPackage(packageName);
        }
        this.element2container.put(cf, package_);
        if (package_ instanceof ByteCodeElement) {
            List<ClassType> ctl = this.containedTypes.get(package_);
            if (ctl == null)
                this.containedTypes.put(package_, ctl = new ArrayList<ClassType>());
            ctl.add(cf);
        }
        List<? extends Field> fl = cf.getFieldInfos();
        for (int i = 0, s = fl.size(); i < s; i++) {
            Field f = fl.get(i);
            f.setProgramModelInfo(this);
            this.element2container.put(f, cf);
            ni.register(f);
        }
        List<? extends Method> ml = cf.getMethodInfos();
        for (int j = 0, m = ml.size(); j < m; j++) {
            Method method = ml.get(j);
            method.setProgramModelInfo(this);
            this.element2container.put(method, cf);
        }
        List<? extends Constructor> cl = cf.getConstructorInfos();
        for (int k = 0, n = cl.size(); k < n; k++) {
            Constructor c = cl.get(k);
            c.setProgramModelInfo(this);
            this.element2container.put(c, cf);
        }
        if (cl.isEmpty() && !cf.isInterface() && !cf.isEnumType() && Character.isJavaIdentifierStart(cf.getName().charAt(0)))
            Debug.log("No constructor defined in " + cf.getFullName());
        String[] innerClasses = cf.getInnerClassNames();
        if (innerClasses != null) {
            String fullName = cf.getFullName();
            for (int i2 = 0; i2 < innerClasses.length; i2++) {
                String cn = innerClasses[i2];
                if (!cn.equals(fullName))
                    ni.getClassType(cn);
            }
        }
        String sname = cf.getSuperClassName();
        String[] inames = cf.getInterfaceNames();
        List<ClassType> list = new ArrayList<ClassType>(inames.length + 1);
        if (sname != null) {
            ClassType ct = ni.getClassType(sname);
            if (ct == null) {
                getErrorHandler().reportError(new MissingClassFileException("Unknown byte code supertype " + sname + " in class " + cf.getFullName(), sname));
            } else {
                ParameterizedType parameterizedType;
                List<TypeArgumentInfo> tais = cf.getSuperClassTypeArguments();
                if (tais != null && tais.size() > 0)
                    parameterizedType = new ParameterizedType(ct, tais);
                list.add(parameterizedType);
            }
        }
        int i1;
        for (i1 = 0; i1 < inames.length; i1++) {
            String iname = inames[i1];
            ClassType ct = ni.getClassType(iname);
            if (ct == null) {
                getErrorHandler().reportError(new MissingClassFileException("Unknown byte code supertype " + iname + " in class " + cf.getFullName(), iname));
            } else {
                ParameterizedType parameterizedType;
                List<TypeArgumentInfo> tais = cf.getSuperInterfaceTypeArguments(i1);
                if (tais != null && tais.size() > 0)
                    parameterizedType = new ParameterizedType(ct, tais);
                list.add(parameterizedType);
            }
        }
        if (list.isEmpty()) {
            ClassType jlo = ni.getJavaLangObject();
            if (cf != jlo)
                list.add(jlo);
        }
        cfce.supertypes = list;
        for (i1 = 0; i1 < list.size(); i1++)
            registerSubtype(cf, list.get(i1));
    }

    public Type getAnnotationType(AnnotationUseInfo au) {
        return getNameInfo().getType(au.getFullReferencedName());
    }

    static class ClassFileCacheEntry extends DefaultProgramModelInfo.ClassTypeCacheEntry {
    }
}
