package recoder.service;

import recoder.AbstractService;
import recoder.ServiceConfiguration;
import recoder.TuningParameters;
import recoder.abstraction.*;
import recoder.bytecode.TypeArgumentInfo;
import recoder.bytecode.TypeParameterInfo;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.declaration.TypeParameterDeclaration;
import recoder.java.reference.TypeReference;
import recoder.util.Debug;

import java.util.*;

public abstract class DefaultProgramModelInfo extends AbstractService implements ProgramModelInfo, TuningParameters {
    final Map<ClassType, ClassTypeCacheEntry> classTypeCache = new HashMap<ClassType, ClassTypeCacheEntry>(256);

    protected DefaultProgramModelInfo(ServiceConfiguration config) {
        super(config);
    }

    private static void removeRange(List list, int from) {
        for (int i = list.size() - 1; i >= from; i--)
            list.remove(i);
    }

    private static void removeRange(List list, int from, int to) {
        if (from > to)
            to ^= from ^= to ^= from;
        int cnt = to - from;
        while (cnt-- > 0)
            list.remove(from);
    }

    final ChangeHistory getChangeHistory() {
        return this.serviceConfiguration.getChangeHistory();
    }

    ErrorHandler getErrorHandler() {
        return this.serviceConfiguration.getProjectSettings().getErrorHandler();
    }

    NameInfo getNameInfo() {
        return this.serviceConfiguration.getNameInfo();
    }

    protected final void updateModel() {
        getChangeHistory().updateModel();
    }

    void registerSubtype(ClassType subtype, ClassType supertype) {
        ProgramModelInfo pmi = supertype.getProgramModelInfo();
        if (pmi != this)
            ((DefaultProgramModelInfo) pmi).registerSubtype(subtype, supertype);
        ClassTypeCacheEntry ctce = this.classTypeCache.get(supertype);
        if (ctce == null)
            this.classTypeCache.put(supertype, ctce = new ClassTypeCacheEntry());
        if (ctce.subtypes == null)
            ctce.subtypes = new HashSet<ClassType>();
        ctce.subtypes.add(subtype);
    }

    void removeSubtype(ClassType subtype, ClassType supertype) {
        ProgramModelInfo pmi = supertype.getProgramModelInfo();
        if (pmi != this)
            ((DefaultProgramModelInfo) pmi).registerSubtype(subtype, supertype);
        ClassTypeCacheEntry ctce = this.classTypeCache.get(supertype);
        if (ctce != null &&
                ctce.subtypes != null)
            ctce.subtypes.remove(subtype);
    }

    public List<ClassType> getSubtypes(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        ProgramModelInfo pmi = ct.getProgramModelInfo();
        if (pmi != this) {
            Debug.assertNonnull(pmi);
            return pmi.getSubtypes(ct);
        }
        ClassTypeCacheEntry ctce = this.classTypeCache.get(ct);
        if (ctce == null)
            this.classTypeCache.put(ct, ctce = new ClassTypeCacheEntry());
        if (ctce.subtypes == null)
            return new ArrayList<ClassType>(0);
        int s = ctce.subtypes.size();
        List<ClassType> result = new ArrayList<ClassType>(s);
        for (ClassType subct : ctce.subtypes)
            result.add(subct);
        return result;
    }

    public List<ClassType> getAllSubtypes(ClassType ct) {
        updateModel();
        List<ClassType> ctl = (new SubTypeTopSort()).getAllTypes(ct);
        ctl.remove(0);
        return ctl;
    }

    public List<ClassType> getAllSupertypes(ClassType ct) {
        updateModel();
        ProgramModelInfo pmi = ct.getProgramModelInfo();
        if (pmi != this) {
            Debug.assertNonnull(pmi);
            return pmi.getAllSupertypes(ct);
        }
        ClassTypeCacheEntry ctce = this.classTypeCache.get(ct);
        if (ctce == null)
            this.classTypeCache.put(ct, ctce = new ClassTypeCacheEntry());
        if (ctce.allSupertypes == null)
            computeAllSupertypes(ct, ctce);
        return ctce.allSupertypes;
    }

    private void computeAllSupertypes(ClassType ct, ClassTypeCacheEntry ctce) {
        ctce.allSupertypes = (new SuperTypeTopSort()).getAllTypes(ct);
    }

    public List<Field> getAllFields(ClassType ct) {
        updateModel();
        ProgramModelInfo pmi = ct.getProgramModelInfo();
        if (pmi != this) {
            Debug.assertNonnull(pmi);
            return pmi.getAllFields(ct);
        }
        ClassTypeCacheEntry ctce = this.classTypeCache.get(ct);
        if (ctce == null)
            this.classTypeCache.put(ct, ctce = new ClassTypeCacheEntry());
        if (ctce.allFields == null)
            computeAllFields(ct, ctce);
        return ctce.allFields;
    }

    private void computeAllFields(ClassType ct, ClassTypeCacheEntry ctce) {
        if (ctce.allSupertypes == null)
            computeAllSupertypes(ct, ctce);
        List<? extends ClassType> classes = ctce.allSupertypes;
        int s = classes.size();
        ArrayList<Field> result = new ArrayList<Field>(s * 4);
        int result_size = 0;
        for (int i = 0; i < s; i++) {
            ClassType c = classes.get(i);
            List<? extends Field> fl = c.getFields();
            if (fl != null) {
                int fs = fl.size();
                for (int j = 0; j < fs; j++) {
                    Field f = fl.get(j);
                    if (isVisibleFor(f, ct)) {
                        String fname = f.getName();
                        int k = 0;
                        while (true) {
                            if (k < result_size) {
                                Field rf = result.get(k);
                                if (rf.getName() == fname)
                                    break;
                                k++;
                                continue;
                            }
                            result.add(f);
                            result_size++;
                            break;
                        }
                    }
                }
            }
        }
        result.trimToSize();
        ctce.allFields = result;
    }

    public List<Method> getAllMethods(ClassType ct) {
        updateModel();
        ProgramModelInfo pmi = ct.getProgramModelInfo();
        if (pmi != this) {
            Debug.assertNonnull(pmi);
            return pmi.getAllMethods(ct);
        }
        ClassTypeCacheEntry ctce = this.classTypeCache.get(ct);
        if (ctce == null)
            this.classTypeCache.put(ct, ctce = new ClassTypeCacheEntry());
        if (ctce.allMethods == null)
            computeAllMethods(ct, ctce);
        return ctce.allMethods;
    }

    private void computeAllMethods(ClassType ct, ClassTypeCacheEntry ctce) {
        if (ctce.allSupertypes == null)
            computeAllSupertypes(ct, ctce);
        List<? extends ClassType> classes = ctce.allSupertypes;
        int s = classes.size();
        ArrayList<Method> result = new ArrayList<Method>(s * 8);
        int result_size = 0;
        for (int i = 0; i < s; i++) {
            ClassType c = classes.get(i);
            List<? extends Method> ml = c.getMethods();
            if (ml != null) {
                int ms = ml.size();
                for (int j = 0; j < ms; j++) {
                    Method m = ml.get(j);
                    if (isVisibleFor(m, ct)) {
                        List<? extends Type> msig = m.getSignature();
                        if (c instanceof ParameterizedType) {
                            ParameterizedType pt = (ParameterizedType) c;
                            List<Type> tmp = new ArrayList<Type>(msig.size());
                            for (int n = 0; n < msig.size(); n++) {
                                Type t = msig.get(n);
                                if (t instanceof TypeParameter) {
                                    int q = 0;
                                    for (; q < pt.getGenericType().getTypeParameters().size() &&
                                            pt.getGenericType().getTypeParameters().get(q) != t; q++)
                                        ;
                                    if (q < pt.getGenericType().getTypeParameters().size()) {
                                        tmp.add(makeParameterizedType(pt.getTypeArgs().get(q)));
                                    } else {
                                        tmp.add(t);
                                    }
                                } else {
                                    tmp.add(t);
                                }
                            }
                            msig = tmp;
                        }
                        String mname = m.getName();
                        int k = 0;
                        while (true) {
                            if (k < result_size) {
                                Method rm = result.get(k);
                                if (rm.getName() == mname) {
                                    List<? extends Type> rsig = rm.getSignature();
                                    if (rsig.equals(msig))
                                        break;
                                }
                                k++;
                                continue;
                            }
                            result.add(m);
                            result_size++;
                            break;
                        }
                    }
                }
            }
        }
        result.trimToSize();
        ctce.allMethods = result;
    }

    private Type makeParameterizedType(TypeArgument ta) {
        ClassType classType;
        Type type1, bt = null;
        switch (ta.getWildcardMode()) {
            case Super:
            case Any:
                classType = getNameInfo().getJavaLangObject();
                break;
            case None:
            case Extends:
                type1 = getBaseType(ta);
                break;
        }
        if (ta.getTypeArguments() == null || ta.getTypeArguments().size() == 0)
            return type1;
        return new ParameterizedType((ClassType) type1, ta.getTypeArguments());
    }

    public List<ClassType> getAllTypes(ClassType ct) {
        updateModel();
        ProgramModelInfo pmi = ct.getProgramModelInfo();
        if (pmi != this) {
            Debug.assertNonnull(pmi);
            return pmi.getAllTypes(ct);
        }
        ClassTypeCacheEntry ctce = this.classTypeCache.get(ct);
        if (ctce == null)
            this.classTypeCache.put(ct, ctce = new ClassTypeCacheEntry());
        if (ctce.allMemberTypes == null)
            computeAllMemberTypes(ct, ctce);
        return ctce.allMemberTypes;
    }

    private void computeAllMemberTypes(ClassType ct, ClassTypeCacheEntry ctce) {
        if (ctce.allSupertypes == null)
            computeAllSupertypes(ct, ctce);
        List<? extends ClassType> classes = ctce.allSupertypes;
        int s = classes.size();
        ArrayList<ClassType> result = new ArrayList<ClassType>(s);
        int result_size = 0;
        for (int i = 0; i < s; i++) {
            ClassType c = classes.get(i);
            List<? extends ClassType> cl = c.getTypes();
            if (cl != null) {
                int cs = cl.size();
                for (int j = 0; j < cs; j++) {
                    ClassType hc = cl.get(j);
                    if (hc != ct && isVisibleFor(hc, ct)) {
                        String cname = hc.getName();
                        int k = 0;
                        while (true) {
                            if (k < result_size) {
                                ClassType rc = result.get(k);
                                if (rc.getName() == cname)
                                    break;
                                k++;
                                continue;
                            }
                            result.add(hc);
                            result_size++;
                            break;
                        }
                    }
                }
            }
        }
        result.trimToSize();
        ctce.allMemberTypes = result;
    }

    public PrimitiveType getPromotedType(PrimitiveType a, PrimitiveType b) {
        if (a == b)
            return a;
        NameInfo ni = getNameInfo();
        if (a == ni.getBooleanType() || b == ni.getBooleanType())
            return null;
        if (a == ni.getDoubleType() || b == ni.getDoubleType())
            return ni.getDoubleType();
        if (a == ni.getFloatType() || b == ni.getFloatType())
            return ni.getFloatType();
        if (a == ni.getLongType() || b == ni.getLongType())
            return ni.getLongType();
        return ni.getIntType();
    }

    public boolean isWidening(PrimitiveType from, PrimitiveType to) {
        if (from == null || to == null)
            return false;
        if (from == to)
            return true;
        NameInfo ni = getNameInfo();
        if (from == ni.getBooleanType() || to == ni.getBooleanType())
            return false;
        if (to == ni.getDoubleType())
            return true;
        if (from == ni.getDoubleType())
            return false;
        if (to == ni.getFloatType())
            return true;
        if (from == ni.getFloatType())
            return false;
        if (to == ni.getLongType())
            return true;
        if (from == ni.getLongType())
            return false;
        if (to == ni.getIntType())
            return true;
        if (from == ni.getIntType())
            return false;
        return (from == ni.getByteType() && to == ni.getShortType());
    }

    public boolean isWidening(ClassType from, ClassType to) {
        return isSubtype(from, to);
    }

    public boolean isWidening(ArrayType from, ArrayType to) {
        Type toBase = to.getBaseType();
        if (toBase == getNameInfo().getJavaLangObject())
            return true;
        Type fromBase = from.getBaseType();
        if (toBase instanceof PrimitiveType)
            return toBase.equals(fromBase);
        return isWidening(fromBase, toBase);
    }

    public boolean isWidening(Type from, Type to) {
        if (from instanceof ClassType) {
            if (to instanceof ClassType)
                return isWidening((ClassType) from, (ClassType) to);
            return from instanceof NullType && (to instanceof ArrayType || to instanceof TypeParameter);
        } else if (from instanceof PrimitiveType) {
            if (to instanceof PrimitiveType)
                return isWidening((PrimitiveType) from, (PrimitiveType) to);
        } else if (from instanceof ArrayType) {
            if (to instanceof ClassType) {
                NameInfo ni = getNameInfo();
                if (to == ni.getJavaLangObject())
                    return true;
                if (to == ni.getJavaLangCloneable())
                    return true;
                return to == ni.getJavaIoSerializable();
            }
            if (to instanceof ArrayType)
                return isWidening((ArrayType) from, (ArrayType) to);
        }
        return false;
    }

    public boolean isSubtype(ClassType a, ClassType b) {
        boolean result = false;
        if (a instanceof ParameterizedType)
            a = ((ParameterizedType) a).getGenericType();
        if (b instanceof ParameterizedType)
            b = ((ParameterizedType) b).getGenericType();
        if (a instanceof TypeParameter && b instanceof TypeParameter) {
            result = true;
        } else if (a != null && b != null) {
            if (a == b || a == getNameInfo().getNullType() || b == getNameInfo().getJavaLangObject()) {
                result = true;
            } else {
                List<? extends ClassType> superA = a.getSupertypes();
                if (superA != null) {
                    int s = superA.size();
                    for (int i = 0; i < s && !result; i++) {
                        ClassType sa = superA.get(i);
                        if (sa == a)
                            getErrorHandler().reportError(new CyclicInheritanceException(a));
                        if (isSubtype(sa, b))
                            result = true;
                    }
                }
            }
        }
        return result;
    }

    public boolean isSupertype(ClassType a, ClassType b) {
        return isSubtype(b, a);
    }

    private final boolean paramMatches(Type ta, Type tb, boolean allowAutoboxing) {
        if (ta == tb)
            return true;
        while (ta instanceof ArrayType && tb instanceof ArrayType) {
            ta = ((ArrayType) ta).getBaseType();
            tb = ((ArrayType) tb).getBaseType();
        }
        if (tb instanceof TypeParameter && ta instanceof ArrayType) {
            TypeParameter tp = (TypeParameter) tb;
            if (tp.getBoundCount() == 0)
                return true;
            if (tp.getBoundCount() > 1)
                return false;
            return tp.getBoundName(0).equals("java.lang.Object");
        }
        if (tb instanceof TypeParameter && ta instanceof ClassType) {
            TypeParameter tp = (TypeParameter) tb;
            for (int i = 0; i < tp.getBoundCount(); i++) {
                ClassType t = getClassTypeFromTypeParameter(tp, i);
                if (t == null) {
                    System.err.println(tp.getBoundName(i));
                    System.err.println("cannot resolve type reference in paramMatches/raw type check... TODO");
                }
                if (!isWidening(ta, t))
                    return false;
            }
            return true;
        }
        if (ta != null && !isWidening(ta, tb)) {
            if (allowAutoboxing) {
                if (ta instanceof PrimitiveType && isWidening(getBoxedType((PrimitiveType) ta), tb))
                    return true;
                if (!(ta instanceof ClassType))
                    return false;
                PrimitiveType unboxedType = getUnboxedType((ClassType) ta);
                return isWidening(unboxedType, tb);
            }
            return false;
        }
        return true;
    }

    private ClassType getClassTypeFromTypeParameter(TypeParameter tp, int i) {
        ClassType t;
        if (tp instanceof TypeParameterDeclaration) {
            TypeParameterDeclaration tpd = (TypeParameterDeclaration) tp;
            SourceInfo si = (SourceInfo) this;
            t = (ClassType) si.getType(tpd.getBounds().get(i));
        } else {
            t = getNameInfo().getClassType(tp.getBoundName(i));
        }
        return t;
    }

    private final boolean internalIsCompatibleSignature(List<Type> a, List<Type> b, boolean allowAutoboxing, boolean isVarArgMethod) {
        int s = b.size();
        int n = a.size();
        if (isVarArgMethod) {
            if (s > n + 1)
                return false;
            if (s == n) {
                Type ta = a.get(s - 1);
                Type tb = ((ArrayType) b.get(s - 1)).getBaseType();
                if (paramMatches(ta, tb, allowAutoboxing))
                    s--;
            } else {
                Type tb = ((ArrayType) b.get(s - 1)).getBaseType();
                for (int j = s - 1; j < n; j++) {
                    Type ta = a.get(j);
                    if (!paramMatches(ta, tb, allowAutoboxing))
                        return false;
                }
                s--;
            }
        } else if (s != n) {
            return false;
        }
        for (int i = 0; i < s; i++) {
            Type ta = a.get(i);
            Type tb = b.get(i);
            if (!paramMatches(ta, tb, allowAutoboxing))
                return false;
        }
        return true;
    }

    public final boolean isCompatibleSignature(List<Type> a, List<Type> b) {
        return internalIsCompatibleSignature(a, b, false, false);
    }

    public final boolean isCompatibleSignature(List<Type> a, List<Type> b, boolean allowAutoboxing, boolean bIsVariableArityMethod) {
        return internalIsCompatibleSignature(a, b, allowAutoboxing, bIsVariableArityMethod);
    }

    public ClassType getBoxedType(PrimitiveType unboxedType) {
        NameInfo ni = getNameInfo();
        if (unboxedType == ni.getBooleanType())
            return ni.getJavaLangBoolean();
        if (unboxedType == ni.getByteType())
            return ni.getJavaLangByte();
        if (unboxedType == ni.getCharType())
            return ni.getJavaLangCharacter();
        if (unboxedType == ni.getShortType())
            return ni.getJavaLangShort();
        if (unboxedType == ni.getIntType())
            return ni.getJavaLangInteger();
        if (unboxedType == ni.getLongType())
            return ni.getJavaLangLong();
        if (unboxedType == ni.getFloatType())
            return ni.getJavaLangFloat();
        if (unboxedType == ni.getDoubleType())
            return ni.getJavaLangDouble();
        throw new Error("Unknown primitive type " + unboxedType.getFullName());
    }

    public PrimitiveType getUnboxedType(ClassType boxedType) {
        NameInfo ni = getNameInfo();
        if (boxedType == ni.getJavaLangBoolean())
            return ni.getBooleanType();
        if (boxedType == ni.getJavaLangByte())
            return ni.getByteType();
        if (boxedType == ni.getJavaLangCharacter())
            return ni.getCharType();
        if (boxedType == ni.getJavaLangShort())
            return ni.getShortType();
        if (boxedType == ni.getJavaLangInteger())
            return ni.getIntType();
        if (boxedType == ni.getJavaLangLong())
            return ni.getLongType();
        if (boxedType == ni.getJavaLangFloat())
            return ni.getFloatType();
        if (boxedType == ni.getJavaLangDouble())
            return ni.getDoubleType();
        return null;
    }

    protected ClassType getOutermostType(ClassType t) {
        ClassTypeContainer classTypeContainer1;
        ClassType classType = t;
        ClassTypeContainer cc = t.getContainer();
        while (cc != null && !(cc instanceof recoder.abstraction.Package)) {
            classTypeContainer1 = cc;
            cc = cc.getContainer();
        }
        return (ClassType) classTypeContainer1;
    }

    public boolean isVisibleFor(Member m, ClassType t) {
        if (t instanceof ParameterizedType)
            t = ((ParameterizedType) t).getGenericType();
        if (m.isPublic())
            return true;
        ClassType mt = m.getContainingClassType();
        if (mt == null)
            return false;
        if (mt == t)
            return true;
        if (m.isPrivate())
            return (getOutermostType(t) == getOutermostType(mt));
        if (mt.getPackage() == t.getPackage())
            return true;
        return m.isProtected() &&
                isSubtype(t, mt);
    }

    public void filterApplicableMethods(List<Method> list, String name, List<Type> signature, ClassType context) {
        boolean allowJava5 = getServiceConfiguration().getProjectSettings().java5Allowed();
        internalFilterApplicableMethods(list, name, signature, context, null, allowJava5);
    }

    Type getBaseType(TypeArgument ta) {
        if (ta.getWildcardMode() == TypeArgument.WildcardMode.Any)
            return getNameInfo().getJavaLangObject();
        if (ta.getWildcardMode() == TypeArgument.WildcardMode.Super)
            return getNameInfo().getJavaLangObject();
        if (ta instanceof TypeArgumentInfo) {
            TypeArgumentInfo tai = (TypeArgumentInfo) ta;
            if (tai.isTypeVariable()) {
                if (tai.getContainingMethodInfo() != null &&
                        tai.getContainingMethodInfo().getTypeParameters() != null)
                    for (TypeParameterInfo tpi : tai.getContainingMethodInfo().getTypeParameters()) {
                        if (tpi.getName().equals(tai.getTypeName()))
                            return tpi;
                    }
                for (TypeParameterInfo tpi : tai.getContainingClassFile().getTypeParameters()) {
                    if (tpi.getName().equals(tai.getTypeName()))
                        return tpi;
                }
                throw new RuntimeException();
            }
            return getNameInfo().getClassType(ta.getTypeName());
        }
        if (ta instanceof TypeArgumentDeclaration) {
            SourceInfo si = getServiceConfiguration().getSourceInfo();
            return si.getType(((TypeArgumentDeclaration) ta).getTypeReferenceAt(0));
        }
        return ((ResolvedTypeArgument) ta).type;
    }

    protected List<Type> replaceTypeArgs(List<Type> sig, List<? extends TypeArgument> typeArgs, List<? extends TypeParameter> typeParams) {
        List<Type> res = new ArrayList<Type>(sig.size());
        for (int i = 0; i < sig.size(); i++)
            res.add((replaceTypeArg(sig.get(i), typeArgs, typeParams)).baseType);
        return res;
    }

    ReplaceTypeArgResult replaceTypeArg(Type t, List<? extends TypeArgument> typeArgs, List<? extends TypeParameter> typeParams) {
        ReplaceTypeArgResult res = new ReplaceTypeArgResult(t, null);
        if (t instanceof TypeParameter)
            for (int j = 0; j < typeParams.size(); j++) {
                if (t.equals(typeParams.get(j))) {
                    res = new ReplaceTypeArgResult(getBaseType(typeArgs.get(j)), typeArgs.get(j).getWildcardMode());
                    break;
                }
            }
        return res;
    }

    private void internalFilterApplicableMethods(List<Method> list, String name, List<Type> signature, ClassType context, List<? extends TypeArgument> typeArguments, boolean allowJava5) {
        Debug.assertNonnull(name, signature, context);
        int s = list.size();
        int i = 0;
        while (i < s) {
            Method m = list.get(i);
            if (!name.equals(m.getName()) || !isVisibleFor(m, context))
                break;
            List<Type> methodSig = m.getSignature();
            if (m.getTypeParameters() != null)
                if (typeArguments != null) {
                    if (typeArguments.size() != m.getTypeParameters().size())
                        break;
                    methodSig = replaceTypeArguments(methodSig, typeArguments, m);
                }
            if (context instanceof ParameterizedType) {
                ParameterizedType pt = (ParameterizedType) context;
                methodSig = replaceTypeArgs(methodSig, pt.getTypeArgs(), pt.getGenericType().getTypeParameters());
            }
            if (!internalIsCompatibleSignature(signature, methodSig, allowJava5, m.isVarArgMethod() & allowJava5))
                break;
            i++;
        }
        if (i < s) {
            int j = i;
            for (; ++i < s; i++) {
                Method m = list.get(i);
                if (!name.equals(m.getName()) || !isVisibleFor(m, context))
                    continue;
                List<Type> methodSig = m.getSignature();
                if (m.getTypeParameters() != null)
                    if (typeArguments != null) {
                        if (typeArguments.size() != m.getTypeParameters().size())
                            continue;
                        methodSig = replaceTypeArguments(methodSig, typeArguments, m);
                    }
                if (context instanceof ParameterizedType) {
                    ParameterizedType pt = (ParameterizedType) context;
                    methodSig = replaceTypeArgs(methodSig, pt.getTypeArgs(), pt.getGenericType().getTypeParameters());
                }
                if (internalIsCompatibleSignature(signature, methodSig, allowJava5, m.isVarArgMethod() & allowJava5)) {
                    list.set(j, m);
                    j++;
                }
                continue;
            }
            removeRange(list, j);
        }
    }

    private List<Type> replaceTypeArguments(List<Type> methodSig, List<? extends TypeArgument> typeArguments, Method m) {
        List<Type> res = new ArrayList<Type>(methodSig.size());
        for (int k = 0; k < methodSig.size(); k++)
            res.add(methodSig.get(k));
        for (int l = 0; l < m.getTypeParameters().size(); l++) {
            TypeParameter tp = m.getTypeParameters().get(l);
            for (int i = 0; i < methodSig.size(); i++) {
                Type param = methodSig.get(i);
                if (!(param instanceof ParameterizedType))
                    if (tp.equals(param)) {
                        Type rep = makeParameterizedType(typeArguments.get(l));
                        res.set(i, rep);
                    }
            }
        }
        return res;
    }

    public void filterMostSpecificMethods(List<Method> list) {
        internalFilterMostSpecificMethods(list, false, false);
    }

    public void filterMostSpecificMethodsPhase2(List<Method> list) {
        internalFilterMostSpecificMethods(list, true, false);
    }

    public void filterMostSpecificMethodsPhase3(List<Method> list) {
        internalFilterMostSpecificMethods(list, true, true);
    }

    private void internalFilterMostSpecificMethods(List<Method> list, boolean allowAutoboxing, boolean allowVarArgs) {
        int size = list.size();
        if (size <= 1)
            return;
        List[] arrayOfList = new List[size];
        arrayOfList[0] = list.get(0).getSignature();
        for (int i = 1; i < size; i++) {
            List<Type> sig = arrayOfList[i] = list.get(i).getSignature();
            if (sig != null)
                for (int m = i - 1; m >= 0; m--) {
                    List<Type> sig2 = arrayOfList[m];
                    if (sig2 != null)
                        if (internalIsCompatibleSignature(sig2, sig, allowAutoboxing, allowVarArgs & list.get(i).isVarArgMethod())) {
                            if (!allowAutoboxing || !internalIsCompatibleSignature(sig, sig2, allowAutoboxing, false))
                                arrayOfList[i] = null;
                        } else if (internalIsCompatibleSignature(sig, sig2, allowAutoboxing, allowVarArgs & list.get(m).isVarArgMethod())) {
                            arrayOfList[m] = null;
                        }
                }
        }
        int k = 0;
        for (int j = size - 1; j >= 0; j--) {
            if (arrayOfList[j] == null) {
                k++;
            } else if (k > 0) {
                removeRange(list, j + 1, j + k + 1);
                k = 0;
            }
        }
        if (k > 0)
            removeRange(list, 0, k);
    }

    public List<? extends Constructor> getConstructors(ClassType ct, List<Type> signature, List<TypeArgumentDeclaration> typeArgs) {
        Debug.assertNonnull(ct, signature);
        if (ct.isInterface()) {
            if (signature.isEmpty())
                return getNameInfo().getJavaLangObject().getConstructors();
            return new ArrayList<Constructor>(0);
        }
        String name = ct.getName();
        name = name.substring(name.lastIndexOf('.') + 1);
        List<Method> meths = internalGetMostSpecificMethods(ct, name, signature, ct.getConstructors(), typeArgs, ct);
        List<Constructor> result = new ArrayList<Constructor>();
        for (int i = 0, s = meths.size(); i < s; i++)
            result.add((Constructor) meths.get(i));
        return result;
    }

    public List<Method> getMethods(ClassType ct, String name, List<Type> signature, List<? extends TypeArgument> typeArgs, ClassType context) {
        return internalGetMostSpecificMethods(ct, name, signature, ct.getAllMethods(), typeArgs, context);
    }

    public List<Method> getMethods(ClassType ct, String name, List<Type> signature, List<? extends TypeArgument> typeArgs) {
        return internalGetMostSpecificMethods(ct, name, signature, ct.getAllMethods(), typeArgs, ct);
    }

    private List<Method> internalGetMostSpecificMethods(ClassType ct, String name, List<Type> signature, List<? extends Method> meths, List<? extends TypeArgument> typeArgs, ClassType context) {
        List<Method> result;
        Debug.assertNonnull(ct, name, signature);
        boolean allowJava5 = Boolean.valueOf(getServiceConfiguration().getProjectSettings().getProperty("java5")).booleanValue();
        if (allowJava5) {
            result = doThreePhaseFilter(meths, signature, name, context, typeArgs);
        } else {
            result = new ArrayList<Method>();
            result.addAll(meths);
            internalFilterApplicableMethods(result, name, signature, context, null, false);
            filterMostSpecificMethods(result);
        }
        return result;
    }

    public List<Method> doThreePhaseFilter(List<? extends Method> methods, List<Type> signature, String name, ClassType context, List<? extends TypeArgument> typeArgs) {
        List<Method> applicableMethods = new ArrayList<Method>(methods.size() + 1);
        applicableMethods.addAll(methods);
        internalFilterApplicableMethods(applicableMethods, name, signature, context, typeArgs, true);
        if (applicableMethods.size() < 2)
            return applicableMethods;
        List<Method> result = new ArrayList<Method>(applicableMethods.size() + 1);
        result.addAll(applicableMethods);
        internalFilterApplicableMethods(result, name, signature, context, typeArgs, false);
        filterMostSpecificMethods(result);
        if (result.size() > 0)
            return result;
        result.addAll(applicableMethods);
        filterMostSpecificMethodsPhase2(result);
        if (result.size() > 0)
            return result;
        result.addAll(applicableMethods);
        filterMostSpecificMethodsPhase3(result);
        return result;
    }

    public void reset() {
        this.classTypeCache.clear();
    }

    protected Type makeParameterizedArrayType(Type t, List<? extends TypeArgument> typeArgs) {
        ArrayType arrayType;
        assert t instanceof ArrayType || t instanceof ClassType;
        Type result = t;
        int dim = 0;
        while (result instanceof ArrayType) {
            result = ((ArrayType) result).getBaseType();
            dim++;
        }
        ParameterizedType parameterizedType = new ParameterizedType((ClassType) result, typeArgs);
        for (int i = 0; i < dim; i++)
            arrayType = getNameInfo().createArrayType(parameterizedType);
        return arrayType;
    }

    public List<Method> getMethods(ClassType ct, String name, List<Type> signature) {
        return getMethods(ct, name, signature, null);
    }

    public List<? extends Constructor> getConstructors(ClassType ct, List<Type> signature) {
        return getConstructors(ct, signature, null);
    }

    static class ResolvedTypeArgument implements TypeArgument {
        final TypeArgument.WildcardMode wm;

        final Type type;

        final List<? extends TypeArgument> typeArgs;

        public ResolvedTypeArgument(TypeArgument.WildcardMode wm, Type type, List<? extends TypeArgument> typeArgs) {
            if (!(type instanceof ArrayType) && !(type instanceof ClassType))
                throw new IllegalArgumentException();
            this.wm = wm;
            this.type = type;
            this.typeArgs = typeArgs;
        }

        public TypeArgument.WildcardMode getWildcardMode() {
            return this.wm;
        }

        public String getTypeName() {
            return this.type.getFullName();
        }

        public List<? extends TypeArgument> getTypeArguments() {
            return this.typeArgs;
        }
    }

    static class ClassTypeCacheEntry {
        List<ClassType> supertypes;

        Set<ClassType> subtypes;

        List<ClassType> allSupertypes;

        List<ClassType> allMemberTypes;

        List<Field> allFields;

        List<Method> allMethods;
    }

    static class SuperTypeTopSort extends ClassTypeTopSort {
        protected final List<ClassType> getAdjacent(ClassType c) {
            return c.getSupertypes();
        }
    }

    static class ReplaceTypeArgResult {
        Type baseType;

        TypeArgument.WildcardMode wildcardMode;

        ReplaceTypeArgResult(Type t, TypeArgument.WildcardMode wm) {
            this.baseType = t;
            this.wildcardMode = wm;
        }
    }

    class SubTypeTopSort extends ClassTypeTopSort {
        protected final List<ClassType> getAdjacent(ClassType c) {
            return DefaultProgramModelInfo.this.getSubtypes(c);
        }
    }
}
