package recoder.service;

import recoder.AbstractService;
import recoder.ModelElement;
import recoder.ServiceConfiguration;
import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.bytecode.ClassFile;
import recoder.bytecode.ReflectionImport;
import recoder.convenience.Format;
import recoder.io.ClassFileRepository;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.java.declaration.AnnotationUseSpecification;
import recoder.java.declaration.TypeParameterDeclaration;
import recoder.util.Debug;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class DefaultNameInfo extends AbstractService implements NameInfo, PropertyChangeListener {
    private static final boolean DEBUG = false;
    private static final int NO_SEARCH = 0;
    private static final int SEARCH_SOURCE = 1;
    private static final int SEARCH_CLASS = 2;
    private static final int SEARCH_REFLECT = 3;
    private final Map<String, Type> name2type = new HashMap<String, Type>(128);
    private final Map<String, Field> name2field = new HashMap<String, Field>(128);
    private final HashMap<ClassType, ArrayList<ArrayType>> removedArrayCache = new HashMap<ClassType, ArrayList<ArrayType>>(128);
    private final PrimitiveType booleanType;
    private final PrimitiveType byteType;
    private final PrimitiveType shortType;
    private final PrimitiveType longType;
    private final PrimitiveType intType;
    private final PrimitiveType floatType;
    private final PrimitiveType doubleType;
    private final PrimitiveType charType;
    private final ProgramModelElement unknownElement;
    private final ClassType unknownClassType;
    private final Type unknownType;
    private final Package unknownPackage;
    private final Method unknownMethod;
    private final Constructor unknownConstructor;
    private final Variable unknownVariable;
    private final Field unknownField;
    private final AnnotationProperty unknownAnnotationProperty;
    private Map<String, Package> name2package = new HashMap<String, Package>(64);
    private ClassType nullType;
    private ClassType javaLangObject;
    private ClassType javaLangString;
    private ClassType javaLangClass;
    private ClassType javaLangCloneable;
    private ClassType javaIoSerializable;
    private ClassType javaLangRunnable;
    private ClassType javaLangBoolean;
    private ClassType javaLangByte;
    private ClassType javaLangCharacter;
    private ClassType javaLangShort;
    private ClassType javaLangInteger;
    private ClassType javaLangLong;
    private ClassType javaLangFloat;
    private ClassType javaLangDouble;
    private ClassType javaLangAnnotationAnnotation;
    private ClassType javaLangEnum;
    private int[] searchMode;

    public DefaultNameInfo(ServiceConfiguration config) {
        super(config);
        this.unknownElement = new UnknownProgramModelElement();
        this.unknownClassType = new UnknownClassType();
        this.unknownType = this.unknownClassType;
        this.unknownPackage = new Package("<unknownPackage>", null);
        this.unknownMethod = new UnknownMethod();
        this.unknownConstructor = new UnknownConstructor();
        this.unknownVariable = new UnknownVariable();
        this.unknownField = new UnknownField();
        this.unknownAnnotationProperty = new UnknownAnnotationProperty();
        this.booleanType = createPrimitiveType("boolean");
        this.byteType = createPrimitiveType("byte");
        this.shortType = createPrimitiveType("short");
        this.longType = createPrimitiveType("long");
        this.intType = createPrimitiveType("int");
        this.floatType = createPrimitiveType("float");
        this.doubleType = createPrimitiveType("double");
        this.charType = createPrimitiveType("char");
    }

    public void initialize(ServiceConfiguration cfg) {
        super.initialize(cfg);
        this.nullType = new NullType(cfg.getImplicitElementInfo());
        createPackage("java.lang");
        cfg.getProjectSettings().addPropertyChangeListener(this);
        updateSearchMode();
    }

    public void propertyChange(PropertyChangeEvent evt) {
        String changedProp = evt.getPropertyName();
        if (changedProp.equals("class.search.mode"))
            updateSearchMode();
    }

    private void updateSearchMode() {
        String prop = this.serviceConfiguration.getProjectSettings().getProperty("class.search.mode");
        if (prop == null)
            prop = "";
        this.searchMode = new int[prop.length()];
        for (int i = 0; i < this.searchMode.length; i++) {
            switch (prop.charAt(i)) {
                case 'S':
                case 's':
                    this.searchMode[i] = 1;
                    break;
                case 'C':
                case 'c':
                    this.searchMode[i] = 2;
                    break;
                case 'R':
                case 'r':
                    this.searchMode[i] = 3;
                    break;
                default:
                    this.searchMode[i] = 0;
                    break;
            }
        }
    }

    private PrimitiveType createPrimitiveType(String name) {
        PrimitiveType res = new PrimitiveType(name, getImplicitElementInfo());
        this.name2type.put(res.getName(), res);
        return res;
    }

    final void updateModel() {
        this.serviceConfiguration.getChangeHistory().updateModel();
    }

    ClassFileRepository getClassFileRepository() {
        return this.serviceConfiguration.getClassFileRepository();
    }

    SourceFileRepository getSourceFileRepository() {
        return this.serviceConfiguration.getSourceFileRepository();
    }

    ByteCodeInfo getByteCodeInfo() {
        return this.serviceConfiguration.getByteCodeInfo();
    }

    SourceInfo getSourceInfo() {
        return this.serviceConfiguration.getSourceInfo();
    }

    ImplicitElementInfo getImplicitElementInfo() {
        return this.serviceConfiguration.getImplicitElementInfo();
    }

    public void register(ClassType ct) {
        Debug.assertNonnull(ct);
        String name = ct.getFullName();
        Object ob = this.name2type.put(name, ct);
        if (ob != null && ob != ct && !(ob instanceof UnknownClassType))
            Debug.log("Internal Warning - Multiple registration of " + Format.toString("%N [%i]", ct) + Format.toString(" --- was: %N [%i]", (ModelElement) ob));
        ArrayList<ArrayType> al = this.removedArrayCache.get(ct);
        if (al != null)
            for (int i = 0; i < al.size(); i++) {
                ArrayType at = al.get(i);
                at.makeNames();
                this.name2type.put(at.getFullName(), at);
            }
    }

    public void register(Field f) {
        Debug.assertNonnull(f);
        this.name2field.put(f.getFullName(), f);
    }

    public ClassType getJavaLangObject() {
        if (this.javaLangObject == null)
            this.javaLangObject = getClassType("java.lang.Object");
        return this.javaLangObject;
    }

    public ClassType getJavaLangString() {
        if (this.javaLangString == null)
            this.javaLangString = getClassType("java.lang.String");
        return this.javaLangString;
    }

    public ClassType getJavaLangBoolean() {
        if (this.javaLangBoolean == null)
            this.javaLangBoolean = getClassType("java.lang.Boolean");
        return this.javaLangBoolean;
    }

    public ClassType getJavaLangByte() {
        if (this.javaLangByte == null)
            this.javaLangByte = getClassType("java.lang.Byte");
        return this.javaLangByte;
    }

    public ClassType getJavaLangCharacter() {
        if (this.javaLangCharacter == null)
            this.javaLangCharacter = getClassType("java.lang.Character");
        return this.javaLangCharacter;
    }

    public ClassType getJavaLangShort() {
        if (this.javaLangShort == null)
            this.javaLangShort = getClassType("java.lang.Short");
        return this.javaLangShort;
    }

    public ClassType getJavaLangInteger() {
        if (this.javaLangInteger == null)
            this.javaLangInteger = getClassType("java.lang.Integer");
        return this.javaLangInteger;
    }

    public ClassType getJavaLangLong() {
        if (this.javaLangLong == null)
            this.javaLangLong = getClassType("java.lang.Long");
        return this.javaLangLong;
    }

    public ClassType getJavaLangFloat() {
        if (this.javaLangFloat == null)
            this.javaLangFloat = getClassType("java.lang.Float");
        return this.javaLangFloat;
    }

    public ClassType getJavaLangDouble() {
        if (this.javaLangDouble == null)
            this.javaLangDouble = getClassType("java.lang.Double");
        return this.javaLangDouble;
    }

    public ClassType getJavaLangClass() {
        if (this.javaLangClass == null)
            this.javaLangClass = getClassType("java.lang.Class");
        return this.javaLangClass;
    }

    public ClassType getJavaLangCloneable() {
        if (this.javaLangCloneable == null)
            this.javaLangCloneable = getClassType("java.lang.Cloneable");
        return this.javaLangCloneable;
    }

    public ClassType getJavaLangRunnable() {
        if (this.javaLangRunnable == null)
            this.javaLangRunnable = getClassType("java.lang.Runnable");
        return this.javaLangRunnable;
    }

    public ClassType getJavaIoSerializable() {
        if (this.javaIoSerializable == null)
            this.javaIoSerializable = getClassType("java.io.Serializable");
        return this.javaIoSerializable;
    }

    public ClassType getJavaLangAnnotationAnnotation() {
        if (this.javaLangAnnotationAnnotation == null)
            this.javaLangAnnotationAnnotation = getClassType("java.lang.annotation.Annotation");
        return this.javaLangAnnotationAnnotation;
    }

    public ClassType getJavaLangEnum() {
        if (this.javaLangEnum == null)
            this.javaLangEnum = getClassType("java.lang.Enum");
        return this.javaLangEnum;
    }

    public ClassType getNullType() {
        return this.nullType;
    }

    public PrimitiveType getShortType() {
        return this.shortType;
    }

    public PrimitiveType getByteType() {
        return this.byteType;
    }

    public PrimitiveType getBooleanType() {
        return this.booleanType;
    }

    public PrimitiveType getIntType() {
        return this.intType;
    }

    public PrimitiveType getLongType() {
        return this.longType;
    }

    public PrimitiveType getFloatType() {
        return this.floatType;
    }

    public PrimitiveType getDoubleType() {
        return this.doubleType;
    }

    public PrimitiveType getCharType() {
        return this.charType;
    }

    public boolean isPackage(String name) {
        updateModel();
        return (this.name2package.get(name) != null);
    }

    public Package createPackage(String name) {
        Package result = this.name2package.get(name);
        if (result == null) {
            result = new Package(name, this.serviceConfiguration.getImplicitElementInfo());
            this.name2package.put(result.getName(), result);
            int ldp = name.lastIndexOf('.');
            if (ldp > 0)
                createPackage(name.substring(0, ldp));
        }
        return result;
    }

    public Package getPackage(String name) {
        Debug.assertNonnull(name);
        updateModel();
        return this.name2package.get(name);
    }

    public List<Package> getPackages() {
        updateModel();
        int size = this.name2package.size();
        List<Package> result = new ArrayList<Package>(size);
        for (Package p : this.name2package.values())
            result.add(p);
        return result;
    }

    public ClassType getClassType(String name) {
        Type result = getType(name);
        if (result instanceof ClassType)
            return (ClassType) result;
        return null;
    }

    public ArrayType createArrayType(Type basetype) {
        String aname = basetype.getFullName() + "[]";
        ArrayType result = (ArrayType) this.name2type.get(aname);
        if (result == null) {
            result = new ArrayType(basetype, this.serviceConfiguration.getImplicitElementInfo());
            this.name2type.put(result.getFullName(), result);
        }
        return result;
    }

    public ArrayType createArrayType(Type basetype, int dimensions) {
        ArrayType arrayType;
        if (dimensions < 1)
            throw new IllegalArgumentException("dimensions must be >= 1");
        Type result = basetype;
        while (dimensions-- > 0)
            arrayType = createArrayType(result);
        return arrayType;
    }

    public ArrayType getArrayType(Type basetype) {
        Debug.assertNonnull(basetype);
        updateModel();
        String aname = basetype.getFullName() + "[]";
        return (ArrayType) this.name2type.get(aname);
    }

    public Type getType(String name) {
        Debug.assertNonnull(name);
        updateModel();
        Type result = this.name2type.get(name);
        if (result != null && !name.equals(result.getFullName())) {
            this.name2type.remove(name);
            result = null;
        }
        if (result == this.unknownType)
            return null;
        if (result == null) {
            if (name.endsWith("]")) {
                result = getType(name.substring(0, name.length() - 2));
                if (result != null)
                    return createArrayType(result);
            }
            if (result == null && loadClass(name)) {
                result = this.name2type.get(name);
                if (result == this.unknownType)
                    return null;
            }
            this.name2type.put(name, (result != null) ? result : this.unknownType);
        }
        return result;
    }

    public List<Type> getTypes() {
        updateModel();
        int size = this.name2type.size();
        List<Type> result = new ArrayList<Type>(size);
        for (Type t : this.name2type.values()) {
            if (t != this.unknownType)
                result.add(t);
        }
        return result;
    }

    public List<ClassType> getTypes(Package pkg) {
        Debug.assertNonnull(pkg);
        updateModel();
        List<ClassType> result = new ArrayList<ClassType>();
        List<Type> tl = getTypes();
        int s = tl.size();
        for (int i = 0; i < s; i++) {
            Type t = tl.get(i);
            if (t instanceof ClassType) {
                ClassType ct = (ClassType) t;
                if (ct.getContainer() == pkg)
                    result.add(ct);
            }
        }
        return result;
    }

    public List<ClassType> getClassTypes() {
        updateModel();
        List<ClassType> result = new ArrayList<ClassType>(this.name2type.size() - 8);
        List<Type> tl = getTypes();
        int s = tl.size();
        for (int i = 0; i < s; i++) {
            Type t = tl.get(i);
            if (t instanceof ClassType)
                result.add((ClassType) t);
        }
        return result;
    }

    public Field getField(String name) {
        Debug.assertNonnull(name);
        updateModel();
        Field result = this.name2field.get(name);
        if (result != null)
            return result;
        int ldp = name.lastIndexOf('.');
        if (ldp == -1)
            return null;
        ClassType ct = getClassType(name.substring(0, ldp));
        if (ct == null)
            return null;
        List<? extends Field> fields = ct.getFields();
        if (fields == null)
            return null;
        String shortname = name.substring(ldp + 1);
        for (int i = 0; i < fields.size(); i++) {
            String fname = fields.get(i).getName();
            if (shortname.equals(fname)) {
                result = fields.get(i);
                if (result != null)
                    break;
            }
        }
        return result;
    }

    public List<Field> getFields() {
        updateModel();
        int size = this.name2field.size();
        List<Field> result = new ArrayList<Field>(size);
        for (Field f : this.name2field.values())
            result.add(f);
        return result;
    }

    private boolean loadClass(String classname) {
        boolean result = false;
        for (int i = 0; !result && i < this.searchMode.length; i++) {
            switch (this.searchMode[i]) {
                case 1:
                    result = loadClassFromSourceCode(classname);
                    break;
                case 2:
                    result = loadClassFromPrecompiledCode(classname);
                    break;
                case 3:
                    result = loadClassByReflection(classname);
                    break;
            }
        }
        return result;
    }

    private boolean loadClassFromPrecompiledCode(String classname) {
        boolean result = false;
        ClassFileRepository cfr = getClassFileRepository();
        ClassFile cf = cfr.getClassFile(classname);
        if (cf != null) {
            getByteCodeInfo().register(cf);
            result = true;
        }
        return result;
    }

    private boolean loadClassFromSourceCode(String classname) {
        boolean result = false;
        CompilationUnit cu = null;
        try {
            cu = getSourceFileRepository().getCompilationUnit(classname);
            if (cu == null) {
                int ldp = classname.lastIndexOf('.');
                if (ldp >= 0) {
                    String shortedname = classname.substring(0, ldp);
                    return (!this.name2package.containsKey(shortedname) && loadClassFromSourceCode(shortedname) && this.name2type.containsKey(classname));
                }
            }
            if (cu != null) {
                getSourceInfo().register(cu);
                result = true;
            }
        } catch (Exception e) {
            Debug.error("Error trying to retrieve source file for type " + classname + "\n" + "Exception was " + e);
            e.printStackTrace();
        }
        return result;
    }

    private boolean loadClassByReflection(String classname) {
        ClassFile cf = ReflectionImport.getClassFile(classname);
        if (cf != null) {
            getByteCodeInfo().register(cf);
            return true;
        }
        return false;
    }

    public String information() {
        int unknown = 0;
        for (Type t : this.name2type.values()) {
            if (t == this.unknownType)
                unknown++;
        }
        return "" + this.name2package.size() + " packages with " + (this.name2type.size() - unknown) + " types (" + unknown + " were pure speculations) and " + this.name2field.size() + " fields";
    }

    public void unregisterClassType(String fullname) {
        unregisterClassType(fullname, false);
    }

    void unregisterClassType(String fullname, boolean recycleArrayEntries) {
        Debug.assertNonnull(fullname);
        ClassType old = (ClassType) this.name2type.remove(fullname);
        fullname = fullname + "[]";
        ArrayList<ArrayType> al = new ArrayList<ArrayType>();
        Type array;
        while ((array = this.name2type.remove(fullname)) != null) {
            if (recycleArrayEntries)
                al.add((ArrayType) array);
            fullname = fullname + "[]";
        }
        if (recycleArrayEntries)
            this.removedArrayCache.put(old, al);
    }

    public void unregisterField(String fullname) {
        Debug.assertNonnull(fullname);
        this.name2field.remove(fullname);
    }

    public void unregisterPackages() {
        Map<String, Package> n2p = new HashMap<String, Package>(64);
        List<ClassFile> cf = getClassFileRepository().getKnownClassFiles();
        for (int i = cf.size() - 1; i >= 0; i--) {
            ClassTypeContainer ctc = cf.get(i).getContainer();
            if (ctc instanceof Package)
                n2p.put(ctc.getFullName(), (Package) ctc);
        }
        this.name2package.clear();
        this.name2package = n2p;
    }

    public ClassType getUnknownClassType() {
        return this.unknownClassType;
    }

    public ProgramModelElement getUnknownElement() {
        return this.unknownElement;
    }

    public Package getUnknownPackage() {
        return this.unknownPackage;
    }

    public Method getUnknownMethod() {
        return this.unknownMethod;
    }

    public Constructor getUnknownConstructor() {
        return this.unknownConstructor;
    }

    public Variable getUnknownVariable() {
        return this.unknownVariable;
    }

    public Field getUnknownField() {
        return this.unknownField;
    }

    public Type getUnknownType() {
        return this.unknownType;
    }

    public AnnotationProperty getUnknownAnnotationProperty() {
        return this.unknownAnnotationProperty;
    }

    void handleTypeRename(ClassType ct, String unregisterFrom, String registerTo) {
        boolean register = false;
        boolean unregister = false;
        Object old = this.name2type.get(registerTo);
        if (old == null || old == this.unknownType)
            register = true;
        old = this.name2type.get(unregisterFrom);
        if (old == ct)
            unregister = true;
        if (unregister)
            this.name2type.remove(unregisterFrom);
        String newArrayName = registerTo + "[]";
        String arrayRemove = unregisterFrom + "[]";
        Type removed;
        while ((removed = this.name2type.remove(arrayRemove)) != null) {
            this.name2type.put(newArrayName, removed);
            arrayRemove = arrayRemove + "[]";
            newArrayName = newArrayName + "[]";
        }
        if (register)
            register(ct);
        this.name2type.put(unregisterFrom, this.unknownClassType);
        List<? extends Field> fl = ct.getFields();
        for (int f = 0, fm = fl.size(); f < fm; f++) {
            Field currentField = fl.get(f);
            String fieldremove = unregisterFrom + "." + currentField.getName();
            if (unregister)
                unregisterField(fieldremove);
            if (register)
                register(currentField);
        }
    }

    class UnknownProgramModelElement implements ProgramModelElement {
        public String getName() {
            return "<unkownElement>";
        }

        public String getFullName() {
            return getName();
        }

        public ProgramModelInfo getProgramModelInfo() {
            return null;
        }

        public void setProgramModelInfo(ProgramModelInfo pmi) {
        }

        public void validate() {
        }

        public UnknownProgramModelElement deepClone() {
            throw new UnsupportedOperationException("Cannot deep-clone implicit information");
        }
    }

    abstract class UnknownMember extends UnknownProgramModelElement implements Member {
        public ClassType getContainingClassType() {
            return DefaultNameInfo.this.unknownClassType;
        }

        public boolean isFinal() {
            return false;
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

        public boolean isStatic() {
            return false;
        }

        public boolean isStrictFp() {
            return false;
        }
    }

    class UnknownClassType extends UnknownMember implements ClassType {
        public String getName() {
            return "<unknownClassType>";
        }

        public ClassTypeContainer getContainer() {
            return null;
        }

        public List<ClassType> getTypes() {
            return new ArrayList<ClassType>(0);
        }

        public Package getPackage() {
            return DefaultNameInfo.this.unknownPackage;
        }

        public boolean isInterface() {
            return false;
        }

        public boolean isOrdinaryInterface() {
            return false;
        }

        public boolean isAnnotationType() {
            return true;
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
            return new ArrayList<ClassType>(0);
        }

        public List<ClassType> getAllSupertypes() {
            List<ClassType> result = new ArrayList<ClassType>();
            result.add(this);
            result.add(DefaultNameInfo.this.getJavaLangObject());
            return result;
        }

        public List<? extends Field> getFields() {
            return DefaultNameInfo.this.getJavaLangObject().getFields();
        }

        public List<Field> getAllFields() {
            return DefaultNameInfo.this.getJavaLangObject().getAllFields();
        }

        public List<Method> getMethods() {
            return DefaultNameInfo.this.getJavaLangObject().getMethods();
        }

        public List<Method> getAllMethods() {
            return DefaultNameInfo.this.getJavaLangObject().getAllMethods();
        }

        public List<Constructor> getConstructors() {
            return new ArrayList<Constructor>(0);
        }

        public List<ClassType> getAllTypes() {
            return new ArrayList<ClassType>(0);
        }

        public List<AnnotationUseSpecification> getAnnotations() {
            return null;
        }

        public List<? extends EnumConstant> getEnumConstants() {
            return null;
        }

        public List<TypeParameterDeclaration> getTypeParameters() {
            return null;
        }
    }

    class UnknownMethod extends UnknownMember implements Method {
        public String getName() {
            return "<unknownMethod>";
        }

        public Package getPackage() {
            return DefaultNameInfo.this.unknownPackage;
        }

        public ClassTypeContainer getContainer() {
            return DefaultNameInfo.this.unknownClassType;
        }

        public List<ClassType> getTypes() {
            return new ArrayList<ClassType>(0);
        }

        public boolean isAbstract() {
            return false;
        }

        public boolean isNative() {
            return false;
        }

        public boolean isStrictFp() {
            return false;
        }

        public boolean isSynchronized() {
            return false;
        }

        public List<ClassType> getExceptions() {
            return new ArrayList<ClassType>(0);
        }

        public Type getReturnType() {
            return DefaultNameInfo.this.unknownType;
        }

        public List<Type> getSignature() {
            return new ArrayList<Type>(0);
        }

        public boolean isVarArgMethod() {
            return false;
        }

        public List<AnnotationUseSpecification> getAnnotations() {
            return null;
        }

        public List<? extends TypeParameter> getTypeParameters() {
            return null;
        }
    }

    class UnknownConstructor extends UnknownMethod implements Constructor {
        public String getName() {
            return "<unknownConstructor>";
        }
    }

    class UnknownVariable extends UnknownProgramModelElement implements Variable {
        public String getName() {
            return "<unknownVariable>";
        }

        public boolean isFinal() {
            return false;
        }

        public Type getType() {
            return DefaultNameInfo.this.unknownType;
        }
    }

    class UnknownField extends UnknownMember implements Field {
        public String getName() {
            return "<unknownField>";
        }

        public Type getType() {
            return DefaultNameInfo.this.unknownType;
        }

        public List<AnnotationUseSpecification> getAnnotations() {
            return null;
        }

        public List<? extends TypeArgument> getTypeArguments() {
            return null;
        }
    }

    class UnknownAnnotationProperty extends UnknownMethod implements AnnotationProperty {
        public Object getDefaultValue() {
            return null;
        }
    }
}
