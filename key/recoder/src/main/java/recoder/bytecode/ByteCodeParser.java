package recoder.bytecode;

import recoder.ParserException;
import recoder.abstraction.ElementValuePair;
import recoder.abstraction.TypeArgument;
import recoder.convenience.Naming;

import java.io.DataInput;
import java.io.DataInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class ByteCodeParser {
    protected static final byte CLASS = 7;
    protected static final byte FIELD_REF = 9;
    protected static final byte METHOD_REF = 10;
    protected static final byte INTERFACE_METHOD_REF = 11;
    protected static final byte STRING = 8;
    protected static final byte INTEGER = 3;
    protected static final byte FLOAT = 4;
    protected static final byte LONG = 5;
    protected static final byte DOUBLE = 6;
    protected static final byte NAME_AND_TYPE = 12;
    protected static final byte UTF8 = 1;
    public boolean readJava5Signatures = true;
    private DataInput in;
    private String className;
    private String fullName;
    private String pathPrefix;
    private String shortName;
    private String superName;
    private int accessFlags;
    private String[] interfaceNames;
    private ArrayList<FieldInfo> fields;
    private ArrayList<MethodInfo> methods;
    private ArrayList<ConstructorInfo> constructors;
    private String[] innerClasses;
    private String[] pool;
    private Object currentDefaultValue;
    private AnnotationUseInfo[][] currentParamAnnotations;
    private ClassFile cf;
    private final String[] longRes;

    private final Set<String> staticInners;

    public ByteCodeParser() {
        this.longRes = new String[256];
        this.staticInners = new HashSet<String>(256);
    }

    static String decodeType(String in) throws ByteCodeFormatException {
        int j, dim = 0;
        int i = 0;
        char c = in.charAt(i);
        if (c == '[') {
            dim = i;
            do {
                i++;
                c = in.charAt(i);
            } while (c == '[');
            dim = i - dim;
        }
        String type = null;
        switch (c) {
            case 'B':
                type = "byte";
                return Naming.toArrayTypeName(type, dim);
            case 'C':
                type = "char";
                return Naming.toArrayTypeName(type, dim);
            case 'D':
                type = "double";
                return Naming.toArrayTypeName(type, dim);
            case 'F':
                type = "float";
                return Naming.toArrayTypeName(type, dim);
            case 'I':
                type = "int";
                return Naming.toArrayTypeName(type, dim);
            case 'J':
                type = "long";
                return Naming.toArrayTypeName(type, dim);
            case 'S':
                type = "short";
                return Naming.toArrayTypeName(type, dim);
            case 'Z':
                type = "boolean";
                return Naming.toArrayTypeName(type, dim);
            case 'V':
                type = "void";
                return Naming.toArrayTypeName(type, dim);
            case 'L':
                j = in.indexOf(';', i);
                type = in.substring(i + 1, j).replace('/', '.').replace('$', '.');
                return Naming.toArrayTypeName(type, dim);
        }
        throw new ByteCodeFormatException("Illegal type code");
    }

    public ClassFile parseClassFile(InputStream is, String location) throws ParserException, IOException {
        return parseClassFile(new DataInputStream(is), location);
    }

    public ClassFile parseClassFile(InputStream is) throws ParserException, IOException {
        return parseClassFile(new DataInputStream(is), (String) null);
    }

    public ClassFile parseClassFile(DataInput inStr) throws ParserException, IOException {
        return parseClassFile(inStr, null);
    }

    public ClassFile parseClassFile(DataInput inStr, String location) throws ParserException, IOException {
        this.cf = new ClassFile();
        this.in = inStr;
        if (inStr.readInt() != -889275714)
            throw new ByteCodeFormatException("Bad magic in bytecode file");
        int minorVersion = inStr.readUnsignedShort();
        int majorVersion = inStr.readUnsignedShort();
        int constantPoolCount = inStr.readUnsignedShort();
        makeConstantPool(constantPoolCount);
        this.accessFlags = inStr.readUnsignedShort();
        this.className = this.pool[inStr.readUnsignedShort()];
        this.className = this.className.replace('/', '.');
        this.fullName = this.className.replace('$', '.');
        int ldp = this.fullName.lastIndexOf('.');
        this.pathPrefix = (ldp > 0) ? this.fullName.substring(0, ldp) : "";
        this.shortName = this.fullName.substring(ldp + 1);
        this.superName = this.pool[inStr.readUnsignedShort()];
        if (this.superName != null)
            this.superName = this.superName.replace('/', '.').replace('$', '.');
        int interfacesCount = inStr.readUnsignedShort();
        this.interfaceNames = new String[interfacesCount];
        for (int i = 0; i < interfacesCount; i++) {
            this.interfaceNames[i] = this.pool[inStr.readUnsignedShort()];
            this.interfaceNames[i] = this.interfaceNames[i].replace('/', '.').replace('$', '.');
        }
        int fieldsCount = inStr.readUnsignedShort();
        this.fields = new ArrayList<FieldInfo>(fieldsCount);
        for (int j = 0; j < fieldsCount; j++)
            this.fields.add(readFieldInfo());
        int methodsCount = inStr.readUnsignedShort();
        this.methods = new ArrayList<MethodInfo>();
        this.constructors = new ArrayList<ConstructorInfo>();
        for (int k = 0; k < methodsCount; k++) {
            MethodInfo minfo = readMethodInfo();
            if (minfo != null)
                if (minfo instanceof ConstructorInfo) {
                    this.constructors.add((ConstructorInfo) minfo);
                } else {
                    this.methods.add(minfo);
                }
        }
        ArrayList<AnnotationUseInfo> annotations = new ArrayList<AnnotationUseInfo>();
        ArrayList<TypeParameterInfo> typeParams = new ArrayList<TypeParameterInfo>();
        ArrayList<List<TypeArgumentInfo>> typeArgList = new ArrayList<List<TypeArgumentInfo>>();
        ArrayList<String> typeNames = new ArrayList<String>();
        this.innerClasses = readAttributesForClassFile(annotations, typeParams, typeArgList, typeNames);
        annotations.trimToSize();
        typeParams.trimToSize();
        this.pool = null;
        this.cf.setLocation(location);
        this.cf.setPhysicalName(this.className);
        this.cf.setFullName(this.fullName);
        this.cf.setName(this.shortName);
        this.cf.setSuperName(this.superName);
        this.cf.setAccessFlags(this.accessFlags);
        this.cf.setInterfaceNames(this.interfaceNames);
        this.fields.trimToSize();
        this.cf.setFields(this.fields);
        this.constructors.trimToSize();
        this.cf.setConstructors(this.constructors);
        this.methods.trimToSize();
        this.cf.setMethods(this.methods);
        this.cf.setInnerClassNames(this.innerClasses);
        this.cf.setAnnotations(annotations);
        this.cf.setTypeParameters(typeParams);
        if (typeArgList.size() > 0) {
            this.cf.superClassTypeArguments = typeArgList.get(0);
            if (typeArgList.size() > 1) {
                ArrayList[] arrayOfArrayList = new ArrayList[typeArgList.size() - 1];
                this.cf.superInterfacesTypeArguments = (List<TypeArgumentInfo>[]) arrayOfArrayList;
                for (int m = 1; m < typeArgList.size(); m++)
                    this.cf.superInterfacesTypeArguments[m - 1] = typeArgList.get(m);
            }
        }
        return this.cf;
    }

    protected void makeConstantPool(int count) throws IOException, ByteCodeFormatException {
        this.pool = new String[count];
        int[] targetIndex = new int[count];
        int i;
        for (i = 1; i < count; i++) {
            int j;
            byte tag = this.in.readByte();
            switch (tag) {
                case 7:
                case 8:
                    j = this.in.readUnsignedShort();
                    if (this.pool[j] != null) {
                        this.pool[i] = this.pool[j];
                        break;
                    }
                    targetIndex[i] = j;
                    break;
                case 9:
                case 10:
                case 11:
                case 12:
                    this.in.skipBytes(4);
                    break;
                case 3:
                    this.pool[i] = String.valueOf(this.in.readInt());
                    break;
                case 4:
                    this.pool[i] = String.valueOf(this.in.readFloat());
                    break;
                case 5:
                    this.pool[i] = String.valueOf(this.in.readLong());
                    i++;
                    break;
                case 6:
                    this.pool[i] = String.valueOf(this.in.readDouble());
                    i++;
                    break;
                case 1:
                    this.pool[i] = this.in.readUTF();
                    break;
                default:
                    throw new ByteCodeFormatException("Bad Constant Pool Type " + tag);
            }
        }
        for (i = 1; i < count; i++) {
            if (targetIndex[i] > 0)
                this.pool[i] = this.pool[targetIndex[i]];
        }
    }

    private String[] decodeTypes(String inStr) throws ByteCodeFormatException {
        int count = 0;
        if (inStr.charAt(0) != '(')
            throw new ByteCodeFormatException("Bad method descriptor");
        boolean returnValue = false;
        int i = 1;
        while (i < inStr.length()) {
            int j, dim = 0;
            char c = inStr.charAt(i);
            if (c == ')') {
                if (returnValue)
                    throw new ByteCodeFormatException("Bad method descriptor");
                returnValue = true;
                i++;
                c = inStr.charAt(i);
            }
            if (c == '[') {
                dim = i;
                do {
                    i++;
                    c = inStr.charAt(i);
                } while (c == '[');
                dim = i - dim;
            }
            String type = null;
            switch (c) {
                case 'B':
                    type = "byte";
                    i++;
                    break;
                case 'C':
                    type = "char";
                    i++;
                    break;
                case 'D':
                    type = "double";
                    i++;
                    break;
                case 'F':
                    type = "float";
                    i++;
                    break;
                case 'I':
                    type = "int";
                    i++;
                    break;
                case 'J':
                    type = "long";
                    i++;
                    break;
                case 'S':
                    type = "short";
                    i++;
                    break;
                case 'Z':
                    type = "boolean";
                    i++;
                    break;
                case 'V':
                    if (!returnValue)
                        throw new ByteCodeFormatException("Void parameter type");
                    type = "void";
                    i++;
                    break;
                case 'L':
                    j = inStr.indexOf(';', i);
                    type = inStr.substring(i + 1, j).replace('/', '.').replace('$', '.');
                    i = j + 1;
                    break;
                default:
                    throw new ByteCodeFormatException("Illegal type code " + c);
            }
            this.longRes[count++] = Naming.toArrayTypeName(type, dim);
        }
        String[] r = new String[count];
        System.arraycopy(this.longRes, 0, r, 0, count);
        return r;
    }

    private String[] readAttributesForMethod(ArrayList<AnnotationUseInfo> emptyListForAnnotations, String[] prereadParams, List<TypeArgumentInfo>[] typeArgs, List<TypeParameterInfo> typeParams) throws IOException, ByteCodeFormatException {
        String[] exceptions = null;
        int count = this.in.readUnsignedShort();
        for (int i = 0; i < count; i++) {
            String name = this.pool[this.in.readUnsignedShort()];
            int length = this.in.readInt();
            if ("Exceptions".equals(name)) {
                if (exceptions != null)
                    throw new ByteCodeFormatException("Multiple exceptions lists");
                int number = this.in.readUnsignedShort();
                exceptions = new String[number];
                for (int j = 0; j < number; j++)
                    exceptions[j] = this.pool[this.in.readUnsignedShort()].replace('/', '.').replace('$', '.');
            } else if ("Signature".equals(name)) {
                if (this.readJava5Signatures) {
                    List[] arrayOfList = readMethodSignature(prereadParams, typeParams);
                    for (int jj = 0; jj < typeArgs.length; jj++)
                        typeArgs[jj] = arrayOfList[jj];
                } else {
                    this.in.skipBytes(length);
                }
            } else if ("RuntimeVisibleAnnotation".equals(name) || "RuntimeInvisibleAnnotation".equals(name)) {
                if (this.readJava5Signatures) {
                    int number = this.in.readUnsignedShort();
                    emptyListForAnnotations.ensureCapacity(number);
                    for (int j = 0; j < number; j++)
                        emptyListForAnnotations.add(readAnnotation());
                } else {
                    this.in.skipBytes(length);
                }
            } else if ("RuntimeVisibleParameterAnnotations".equals(name) || "RuntimeInvisibleParameterAnnotations".equals(name)) {
                if (this.readJava5Signatures) {
                    int paramNum = this.in.readUnsignedByte();
                    this.currentParamAnnotations = new AnnotationUseInfo[paramNum][];
                    for (int j = 0; j < paramNum; j++) {
                        int number = this.in.readUnsignedShort();
                        this.currentParamAnnotations[j] = new AnnotationUseInfo[number];
                        for (int k = 0; k < number; k++)
                            this.currentParamAnnotations[j][k] = readAnnotation();
                    }
                } else {
                    this.in.skipBytes(length);
                }
            } else if ("AnnotationDefault".equals(name)) {
                if (this.readJava5Signatures) {
                    if (this.currentDefaultValue != null)
                        throw new ByteCodeFormatException("Multiple annotation defaults!");
                    this.currentDefaultValue = readElementValue();
                } else {
                    this.in.skipBytes(length);
                }
            } else {
                this.in.skipBytes(length);
            }
        }
        return exceptions;
    }

    private String[] readAttributesForClassFile(ArrayList<AnnotationUseInfo> emptyListForAnnotations, List<TypeParameterInfo> emptyListForTypeParams, List<List<TypeArgumentInfo>> emptyListForTypeArgumentLists, List<String> emptyListForTypeNames) throws IOException, ByteCodeFormatException {
        String[] innerClassesRes = null;
        int count = this.in.readUnsignedShort();
        for (int i = 0; i < count; i++) {
            String name = this.pool[this.in.readUnsignedShort()];
            int length = this.in.readInt();
            if ("InnerClasses".equals(name)) {
                if (innerClassesRes != null)
                    throw new ByteCodeFormatException("Multiple inner classes lists");
                int number = this.in.readUnsignedShort();
                innerClassesRes = new String[number];
                int k = 0;
                for (int j = 0; j < number; j++) {
                    String s = readInnerClassInfo();
                    if (s != null)
                        innerClassesRes[k++] = s;
                }
                if (k != number) {
                    String[] tmpInnerClassesRes = new String[k];
                    System.arraycopy(innerClassesRes, 0, tmpInnerClassesRes, 0, k);
                    innerClassesRes = tmpInnerClassesRes;
                }
            } else if ("RuntimeVisibleAnnotations".equals(name) || "RuntimeInvisibleAnnotations".equals(name)) {
                if (this.readJava5Signatures) {
                    if (emptyListForAnnotations.size() != 0)
                        throw new ByteCodeFormatException("Multiple annotation lists");
                    int number = this.in.readUnsignedShort();
                    emptyListForAnnotations.ensureCapacity(number);
                    for (int j = 0; j < number; j++)
                        emptyListForAnnotations.add(readAnnotation());
                } else {
                    this.in.skipBytes(length);
                }
            } else if ("EnclosingMethod".equals(name)) {
                this.in.skipBytes(length);
            } else if ("Synthetic".equals(name)) {
                this.in.skipBytes(length);
            } else if ("SourceFile".equals(name)) {
                this.in.skipBytes(length);
            } else if ("Signature".equals(name)) {
                if (this.readJava5Signatures) {
                    ReadClassSignatureResult res = readClassSignature();
                    for (TypeParameterInfo tai : res.typeParams)
                        emptyListForTypeParams.add(tai);
                    for (List<TypeArgumentInfo> tai : res.typeArgumentArray)
                        emptyListForTypeArgumentLists.add(tai);
                    for (String n : res.typeNameArray)
                        emptyListForTypeNames.add(n);
                } else {
                    this.in.skipBytes(length);
                }
            } else if ("Deprecated".equals(name)) {
                this.in.skipBytes(length);
            } else {
                this.in.skipBytes(length);
            }
        }
        return innerClassesRes;
    }

    private String[] readAttributesForField(ArrayList<AnnotationUseInfo> emptyListForAnnotations, List<TypeArgumentInfo> emptyListForTypeArgs) throws IOException, ByteCodeFormatException {
        assert emptyListForAnnotations != null && emptyListForAnnotations.isEmpty();
        String constant = null;
        String type = null;
        int count = this.in.readUnsignedShort();
        for (int i = 0; i < count; i++) {
            String id = this.pool[this.in.readUnsignedShort()];
            int length = this.in.readInt();
            if ("ConstantValue".equals(id)) {
                if (constant != null)
                    throw new ByteCodeFormatException("Multiple constant values for field");
                constant = this.pool[this.in.readUnsignedShort()];
            } else if ("Signature".equals(id)) {
                if (this.readJava5Signatures) {
                    type = readFieldSignature(this.pool[this.in.readUnsignedShort()], emptyListForTypeArgs);
                } else {
                    this.in.skipBytes(length);
                }
            } else if ("RuntimeVisibleAnnotation".equals(id) || "RuntimeInvisibleAnnotation".equals(id)) {
                if (this.readJava5Signatures) {
                    int number = this.in.readUnsignedShort();
                    emptyListForAnnotations.ensureCapacity(number);
                    for (int j = 0; j < number; j++)
                        emptyListForAnnotations.add(readAnnotation());
                } else {
                    this.in.skipBytes(length);
                }
            } else {
                this.in.skipBytes(length);
            }
        }
        return new String[]{constant, type};
    }

    FieldInfo readFieldInfo() throws IOException, ByteCodeFormatException {
        int fieldAccessFlags = this.in.readUnsignedShort();
        String name = this.pool[this.in.readUnsignedShort()];
        String type = decodeType(this.pool[this.in.readUnsignedShort()]);
        ArrayList<AnnotationUseInfo> annotations = new ArrayList<AnnotationUseInfo>();
        ArrayList<TypeArgumentInfo> typeArgs = new ArrayList<TypeArgumentInfo>();
        String[] tmp = readAttributesForField(annotations, typeArgs);
        String constant = tmp[0];
        if (tmp[1] != null)
            type = tmp[1];
        FieldInfo res = new FieldInfo(fieldAccessFlags, name, type, this.cf, constant, typeArgs);
        res.setAnnotations(annotations);
        return res;
    }

    MethodInfo readMethodInfo() throws IOException, ByteCodeFormatException {
        MethodInfo res;
        int methAccessFlags = this.in.readUnsignedShort();
        String name = this.pool[this.in.readUnsignedShort()];
        boolean isConstructor = "<init>".equals(name);
        boolean isInitializer = false;
        if (isConstructor) {
            name = this.shortName;
        } else {
            isInitializer = "<clinit>".equals(name);
        }
        String[] types = decodeTypes(this.pool[this.in.readUnsignedShort()]);
        ArrayList<AnnotationUseInfo> annotations = new ArrayList<AnnotationUseInfo>();
        this.currentDefaultValue = null;
        this.currentParamAnnotations = null;
        List[] arrayOfList = new List[types.length];
        ArrayList<TypeParameterInfo> typeParams = new ArrayList<TypeParameterInfo>();
        String[] exceptions = readAttributesForMethod(annotations, types, arrayOfList, typeParams);
        String rtype = types[types.length - 1];
        int firstParam = 0;
        int paramCount = types.length - 1;
        if (isConstructor && types[0].equals(this.pathPrefix) && !this.staticInners.contains(this.fullName)) {
            firstParam = 1;
            paramCount--;
        }
        String[] ptypes = new String[paramCount];
        System.arraycopy(types, firstParam, ptypes, 0, paramCount);
        if (isInitializer)
            return null;
        if (isConstructor) {
            res = new ConstructorInfo(methAccessFlags, name, ptypes, exceptions, this.cf);
        } else if ((this.accessFlags & 0x2000) != 0) {
            res = new AnnotationPropertyInfo(methAccessFlags, rtype, name, this.cf, this.currentDefaultValue);
        } else {
            res = new MethodInfo(methAccessFlags, rtype, name, ptypes, exceptions, this.cf);
        }
        res.setAnnotations(annotations);
        res.paramAnnotations = this.currentParamAnnotations;
        if (arrayOfList.length != 0) {
            setTypeArgParentRec(arrayOfList, res);
            res.paramTypeArgs = (List<TypeArgumentInfo>[]) arrayOfList;
        }
        if (typeParams.size() != 0) {
            typeParams.trimToSize();
            res.typeParms = typeParams;
        }
        return res;
    }

    private void setTypeArgParentRec(List<? extends TypeArgument>[] typeArgs, MethodInfo res) {
        for (int i = 0; i < typeArgs.length; i++) {
            if (typeArgs[i] != null)
                setTypeArgParentRec(typeArgs[i], res);
        }
    }

    private void setTypeArgParentRec(List<? extends TypeArgument> typeArgs, MethodInfo res) {
        for (TypeArgument ta : typeArgs) {
            TypeArgumentInfo tai = (TypeArgumentInfo) ta;
            tai.parent = res;
            if (tai.typeArgs != null)
                setTypeArgParentRec(tai.typeArgs, res);
        }
    }

    public String readInnerClassInfo() throws IOException {
        String name = this.pool[this.in.readUnsignedShort()];
        if (name != null)
            name = name.replace('/', '.').replace('$', '.');
        this.in.readUnsignedShort();
        this.in.readUnsignedShort();
        int innerClassAccessFlags = this.in.readUnsignedShort();
        if (name != null && (innerClassAccessFlags & 0x8) != 0)
            this.staticInners.add(name);
        if (name != null)
            if (!this.fullName.equals(name.substring(0, name.lastIndexOf('.')))) {
                name = null;
            } else if (!Character.isJavaIdentifierStart(name.charAt(name.lastIndexOf('.') + 1))) {
                name = null;
            }
        return name;
    }

    private Object readElementValue() throws IOException, ByteCodeFormatException {
        Object res;
        String typename, constname, tr;
        int num, i, tag = this.in.readByte();
        switch (tag) {
            case 66:
                res = Byte.valueOf(this.pool[this.in.readUnsignedShort()]);
                return res;
            case 67:
                res = Character.valueOf(this.pool[this.in.readUnsignedShort()].toCharArray()[0]);
                return res;
            case 68:
                res = Double.valueOf(this.pool[this.in.readUnsignedShort()]);
                return res;
            case 70:
                res = Float.valueOf(this.pool[this.in.readUnsignedShort()]);
                return res;
            case 73:
                res = Integer.valueOf(this.pool[this.in.readUnsignedShort()]);
                return res;
            case 74:
                res = Long.valueOf(this.pool[this.in.readUnsignedShort()]);
                return res;
            case 83:
                res = Short.valueOf(this.pool[this.in.readUnsignedShort()]);
                return res;
            case 90:
                res = Boolean.valueOf(this.pool[this.in.readUnsignedShort()]);
                return res;
            case 115:
                res = this.pool[this.in.readUnsignedShort()];
                return res;
            case 101:
                typename = this.pool[this.in.readUnsignedShort()];
                constname = this.pool[this.in.readUnsignedShort()];
                res = new EnumConstantReferenceInfo(typename, constname);
                return res;
            case 99:
                tr = this.pool[this.in.readUnsignedShort()];
                tr.replace('/', '.').replace('$', '.');
                res = new TypeNameReferenceInfo(tr);
                return res;
            case 64:
                res = readAnnotation();
                return res;
            case 91:
                num = this.in.readUnsignedShort();
                res = new Object[num];
                for (i = 0; i < num; i++)
                    ((Object[]) res)[i] = readElementValue();
                return res;
        }
        throw new ByteCodeFormatException("Illegal tag in element-value: " + tag);
    }

    private AnnotationUseInfo readAnnotation() throws IOException, ByteCodeFormatException {
        String name = this.pool[this.in.readUnsignedShort()];
        if (name == null)
            throw new ByteCodeFormatException();
        name = name.replace('/', '.').replace('$', '.').substring(1, name.length() - 1);
        int number = this.in.readUnsignedShort();
        List<ElementValuePair> evpl = new ArrayList<ElementValuePair>(number);
        for (int i = 0; i < number; i++) {
            String elementName = this.pool[this.in.readUnsignedShort()];
            Object value = readElementValue();
            ElementValuePairInfo evpi = new ElementValuePairInfo(elementName, value, name);
            evpl.add(evpi);
        }
        return new AnnotationUseInfo(name, evpl);
    }

    private ReadClassSignatureResult readClassSignature() throws IOException, ByteCodeFormatException {
        ReadClassSignatureResult res = new ReadClassSignatureResult();
        String sig = this.pool[this.in.readUnsignedShort()];
        int start = 0;
        if (sig.charAt(0) == '<') {
            res.typeParams = readFormalTypeParameters(sig);
            start = 1;
            for (int o = 1; o > 0; start++) {
                if (sig.charAt(start) == '<') {
                    o++;
                } else if (sig.charAt(start) == '>') {
                    o--;
                }
            }
        }
        List<List<TypeArgumentInfo>> l1 = new ArrayList<List<TypeArgumentInfo>>();
        List<String> l2 = new ArrayList<String>();
        while (start != sig.length()) {
            int end = start;
            int o = 0;
            while (sig.charAt(++end) != ';' || o > 0) {
                if (sig.charAt(end) == '<') {
                    o++;
                    continue;
                }
                if (sig.charAt(end) == '>')
                    o--;
            }
            end++;
            String sig2 = sig.substring(start, end);
            ArrayList<TypeArgumentInfo> ral = new ArrayList<TypeArgumentInfo>();
            l2.add(readFieldSignature(sig2, ral));
            l1.add(ral);
            start = end;
        }
        if (res.typeParams == null)
            res.typeParams = new ArrayList<TypeParameterInfo>();
        res.typeArgumentArray = l1;
        res.typeNameArray = l2;
        return res;
    }

    private List<TypeParameterInfo> readFormalTypeParameters(String sig) throws ByteCodeFormatException {
        List<TypeParameterInfo> res = new ArrayList<TypeParameterInfo>();
        int rpos = 1;
        int cnt = 0;
        while (sig.charAt(rpos) != '>') {
            cnt++;
            int lpos = rpos;
            while (sig.charAt(rpos) != ':')
                rpos++;
            String paramName = sig.substring(lpos, rpos);
            List<String> boundNames = new ArrayList<String>();
            List<List<TypeArgumentInfo>> boundArgs = new ArrayList<List<TypeArgumentInfo>>();
            while (true) {
                String typeName;
                lpos = ++rpos;
                if (sig.charAt(lpos) == '[')
                    throw new ByteCodeFormatException();
                switch (sig.charAt(lpos)) {
                    case ':':
                        typeName = "java.lang.Object";
                        break;
                    case 'L':
                        while (sig.charAt(rpos) != ';')
                            rpos++;
                        typeName = sig.substring(lpos + 1, rpos).replace('/', '.');
                        rpos++;
                        break;
                    case 'T':
                        throw new UnsupportedOperationException("TODO");
                    default:
                        throw new ByteCodeFormatException();
                }
                int idx = typeName.indexOf('<');
                List<TypeArgumentInfo> typeArgs = null;
                if (idx != -1) {
                    typeArgs = makeTypeArgs(typeName.substring(idx));
                    typeName = typeName.substring(0, idx);
                    rpos += 2;
                }
                boundNames.add(typeName);
                boundArgs.add(typeArgs);
                if (sig.charAt(rpos) != ':') {
                    String[] bn = new String[boundNames.size()];
                    boundNames.toArray(bn);
                    List[] arrayOfList = new List[boundArgs.size()];
                    boundArgs.toArray(arrayOfList);
                    TypeParameterInfo n = new TypeParameterInfo(paramName, bn, arrayOfList, this.cf);
                    res.add(n);
                }
            }
        }
        return res;
    }

    private List<TypeArgumentInfo> makeTypeArgs(String tn) throws ByteCodeFormatException {
        ArrayList<TypeArgumentInfo> res = new ArrayList<TypeArgumentInfo>();
        assert tn.charAt(0) == '<';
        int pos = 1;
        while (true) {
            TypeArgument.WildcardMode wm;
            String typeName = null;
            switch (tn.charAt(pos)) {
                case '+':
                    wm = TypeArgument.WildcardMode.Extends;
                    pos++;
                    break;
                case '-':
                    wm = TypeArgument.WildcardMode.Super;
                    pos++;
                    break;
                case '*':
                    wm = TypeArgument.WildcardMode.Any;
                    pos++;
                    break;
                default:
                    wm = TypeArgument.WildcardMode.None;
                    break;
            }
            if (wm != TypeArgument.WildcardMode.Any) {
                int o;
                boolean isTypeVariable = false;
                int dim = 0;
                while (tn.charAt(pos) == '[') {
                    dim++;
                    pos++;
                }
                int rpos = pos;
                switch (tn.charAt(pos)) {
                    case 'L':
                        o = 1;
                        while (rpos < tn.length() && o > 0 && (tn.charAt(rpos) != ';' || o != 1)) {
                            if (tn.charAt(rpos) == '<')
                                o++;
                            if (tn.charAt(rpos) == '>')
                                o--;
                            rpos++;
                        }
                        typeName = tn.substring(pos + 1, rpos).replace('/', '.');
                        if (typeName.equals(""))
                            typeName = "java.lang.Object";
                        while (typeName.endsWith(";") || typeName.endsWith(">"))
                            typeName = typeName.substring(0, typeName.length() - 1);
                        typeName = Naming.toArrayTypeName(typeName, dim);
                        rpos++;
                        break;
                    case 'T':
                        while (rpos < tn.length() && Character.isJavaIdentifierPart(tn.charAt(rpos)))
                            rpos++;
                        typeName = tn.substring(pos + 1, rpos);
                        typeName = Naming.toArrayTypeName(typeName, dim);
                        isTypeVariable = true;
                        rpos++;
                        break;
                    case 'B':
                        if (dim == 0)
                            throw new ByteCodeFormatException("primitive type not allowed as type argument");
                        typeName = "byte";
                        rpos++;
                        break;
                    case 'C':
                        if (dim == 0)
                            throw new ByteCodeFormatException("primitive type not allowed as type argument");
                        typeName = "char";
                        rpos++;
                        break;
                    case 'D':
                        if (dim == 0)
                            throw new ByteCodeFormatException("primitive type not allowed as type argument");
                        typeName = "double";
                        rpos++;
                        break;
                    case 'F':
                        if (dim == 0)
                            throw new ByteCodeFormatException("primitive type not allowed as type argument");
                        typeName = "float";
                        rpos++;
                        break;
                    case 'I':
                        if (dim == 0)
                            throw new ByteCodeFormatException("primitive type not allowed as type argument");
                        typeName = "int";
                        rpos++;
                        break;
                    case 'J':
                        if (dim == 0)
                            throw new ByteCodeFormatException("primitive type not allowed as type argument");
                        typeName = "long";
                        rpos++;
                        break;
                    case 'S':
                        if (dim == 0)
                            throw new ByteCodeFormatException("primitive type not allowed as type argument");
                        typeName = "short";
                        rpos++;
                        break;
                    case 'Z':
                        if (dim == 0)
                            throw new ByteCodeFormatException("primitive type not allowed as type argument");
                        typeName = "boolean";
                        rpos++;
                        break;
                    default:
                        throw new ByteCodeFormatException();
                }
                int idx = typeName.indexOf('<');
                List<TypeArgumentInfo> typeArgs = null;
                if (idx != -1) {
                    typeArgs = makeTypeArgs(typeName.substring(idx));
                    typeName = typeName.substring(0, idx);
                    typeName = Naming.toArrayTypeName(typeName, dim);
                }
                res.add(new TypeArgumentInfo(wm, typeName.replace('$', '.'), typeArgs, this.cf, isTypeVariable));
                pos = rpos;
            } else {
                res.add(new TypeArgumentInfo(wm, null, null, this.cf, false));
            }
            if (pos >= tn.length()) {
                res.trimToSize();
                return res;
            }
        }
    }

    private String readFieldSignature(String sig, List<TypeArgumentInfo> emptyListForTypeArgs) throws IOException, ByteCodeFormatException {
        int lpos, idx;
        String res = null;
        int rpos = sig.indexOf('(') + 1;
        int dim = 0;
        while (sig.charAt(rpos) == '[') {
            dim++;
            rpos++;
        }
        switch (sig.charAt(rpos)) {
            case 'L':
                lpos = rpos;
                while (sig.charAt(rpos) != ';') {
                    if (sig.charAt(rpos) == '<') {
                        int talpos = rpos;
                        int o = 1;
                        while (o > 0) {
                            rpos++;
                            if (sig.charAt(rpos) == '<')
                                o++;
                            if (sig.charAt(rpos) == '>')
                                o--;
                        }
                        String targs = sig.substring(talpos, rpos);
                        emptyListForTypeArgs.addAll(makeTypeArgs(targs));
                    }
                    rpos++;
                }
                idx = sig.indexOf('<');
                res = Naming.toArrayTypeName(sig.substring(lpos + 1, (idx == -1) ? (sig.length() - 1) : idx).replace('/', '.'), dim);
                rpos++;
                return res;
            case 'T':
                lpos = rpos;
                while (sig.charAt(rpos) != ';')
                    rpos++;
                res = Naming.toArrayTypeName(sig.substring(lpos + 1, rpos), dim);
                rpos++;
                return res;
            case 'B':
            case 'C':
            case 'D':
            case 'F':
            case 'I':
            case 'J':
            case 'S':
            case 'Z':
                rpos++;
                return res;
        }
        rpos++;
        return res;
    }

    private List<TypeArgumentInfo>[] readMethodSignature(String[] prereadParams, List<TypeParameterInfo> listForTypeParams) throws IOException, ByteCodeFormatException {
        ArrayList[] arrayOfArrayList = new ArrayList[prereadParams.length];
        String sig = this.pool[this.in.readUnsignedShort()];
        if (sig.charAt(0) == '<')
            listForTypeParams.addAll(readFormalTypeParameters(sig));
        int cur = -1;
        int rpos = sig.indexOf('(') + 1;
        boolean hasReturnValue = false;
        while (!hasReturnValue) {
            int lpos;
            cur++;
            if (sig.charAt(rpos) == ')') {
                hasReturnValue = true;
                rpos++;
            }
            int dim = 0;
            while (sig.charAt(rpos) == '[') {
                dim++;
                rpos++;
            }
            switch (sig.charAt(rpos)) {
                case 'L':
                    lpos = rpos;
                    while (sig.charAt(rpos) != ';') {
                        if (sig.charAt(rpos) == '<') {
                            int talpos = rpos;
                            int o = 1;
                            while (o > 0) {
                                rpos++;
                                if (sig.charAt(rpos) == '<')
                                    o++;
                                if (sig.charAt(rpos) == '>')
                                    o--;
                            }
                            String targs = sig.substring(talpos, rpos);
                            arrayOfArrayList[cur] = (ArrayList) makeTypeArgs(targs);
                        }
                        rpos++;
                    }
                    rpos++;
                    continue;
                case 'T':
                    lpos = rpos;
                    while (sig.charAt(rpos) != ';')
                        rpos++;
                    prereadParams[cur] = Naming.toArrayTypeName(sig.substring(lpos + 1, rpos), dim);
                    rpos++;
                    continue;
                case 'B':
                case 'C':
                case 'D':
                case 'F':
                case 'I':
                case 'J':
                case 'S':
                case 'Z':
                    rpos++;
                    continue;
            }
            rpos++;
        }
        return (List<TypeArgumentInfo>[]) arrayOfArrayList;
    }

    private static class ReadClassSignatureResult {
        List<TypeParameterInfo> typeParams;

        List<List<TypeArgumentInfo>> typeArgumentArray;

        List<String> typeNameArray;

        private ReadClassSignatureResult() {
        }
    }
}
