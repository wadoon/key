package recoder.convenience;

import recoder.abstraction.ClassTypeContainer;
import recoder.abstraction.Field;
import recoder.java.CompilationUnit;
import recoder.java.Identifier;
import recoder.java.PackageSpecification;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.*;
import recoder.util.Debug;

import java.io.File;
import java.util.HashSet;
import java.util.Set;

public abstract class Naming {
    private static final Set<String> KEYWORDS = new HashSet<String>();

    static {
        KEYWORDS.add("abstract");
        KEYWORDS.add("default");
        KEYWORDS.add("if");
        KEYWORDS.add("private");
        KEYWORDS.add("throw");
        KEYWORDS.add("boolean");
        KEYWORDS.add("do");
        KEYWORDS.add("implements");
        KEYWORDS.add("protected");
        KEYWORDS.add("throws");
        KEYWORDS.add("break");
        KEYWORDS.add("double");
        KEYWORDS.add("import");
        KEYWORDS.add("public");
        KEYWORDS.add("transient");
        KEYWORDS.add("byte");
        KEYWORDS.add("else");
        KEYWORDS.add("instanceof");
        KEYWORDS.add("return");
        KEYWORDS.add("try");
        KEYWORDS.add("case");
        KEYWORDS.add("extends");
        KEYWORDS.add("int");
        KEYWORDS.add("short");
        KEYWORDS.add("void");
        KEYWORDS.add("catch");
        KEYWORDS.add("final");
        KEYWORDS.add("interface");
        KEYWORDS.add("static");
        KEYWORDS.add("volatile");
        KEYWORDS.add("char");
        KEYWORDS.add("finally");
        KEYWORDS.add("long");
        KEYWORDS.add("super");
        KEYWORDS.add("while");
        KEYWORDS.add("class");
        KEYWORDS.add("float");
        KEYWORDS.add("native");
        KEYWORDS.add("switch");
        KEYWORDS.add("const");
        KEYWORDS.add("for");
        KEYWORDS.add("new");
        KEYWORDS.add("synchronized");
        KEYWORDS.add("continue");
        KEYWORDS.add("goto");
        KEYWORDS.add("package");
        KEYWORDS.add("this");
        KEYWORDS.add("assert");
    }

    public static boolean hasLowerCaseBegin(String str) {
        return str.length() != 0 && Character.isLowerCase(str.charAt(0));
    }

    public static String makeLowerCaseBegin(String str) {
        return (str.length() == 0) ? str : (Character.toLowerCase(str.charAt(0)) + str.substring(1));
    }

    public static boolean hasUpperCaseBegin(String str) {
        return str.length() != 0 && Character.isUpperCase(str.charAt(0));
    }

    public static String makeUpperCaseBegin(String str) {
        return (str.length() == 0) ? str : (Character.toUpperCase(str.charAt(0)) + str.substring(1));
    }

    public static String createMemberName(String base) {
        return makeLowerCaseBegin(base);
    }

    public static Identifier createMemberName(Identifier base) {
        String text = base.getText();
        return hasLowerCaseBegin(text) ? base.deepClone() : base.getFactory().createIdentifier(makeLowerCaseBegin(text));
    }

    public static String createClassName(String base) {
        return makeUpperCaseBegin(base);
    }

    public static Identifier createClassName(Identifier base) {
        String text = base.getText();
        return hasUpperCaseBegin(text) ? base.deepClone() : base.getFactory().createIdentifier(makeUpperCaseBegin(text));
    }

    public static String createPackageName(String base) {
        return base.toLowerCase();
    }

    public static Identifier createPackageName(Identifier base) {
        return base.getFactory().createIdentifier(base.getText().toLowerCase());
    }

    public static String createConstantName(String base) {
        return base.toUpperCase();
    }

    public static Identifier createConstantName(Identifier base) {
        return base.getFactory().createIdentifier(base.getText().toUpperCase());
    }

    public static String makeFilename(String logicalName) {
        return logicalName.replace('.', File.separatorChar);
    }

    public static String dot(String prefix, String suffix) {
        if (prefix == null)
            prefix = "";
        if (suffix == null)
            suffix = "";
        int plen = prefix.length();
        int slen = suffix.length();
        int tlen = plen + slen + 1;
        char[] buf = new char[tlen];
        buf[plen] = '.';
        prefix.getChars(0, plen, buf, 0);
        suffix.getChars(0, slen, buf, plen + 1);
        return new String(buf, 0, tlen);
    }

    public static String toArrayTypeName(String basename, int dimensions) {
        if (dimensions == 0 || basename == null)
            return basename;
        int len = basename.length();
        char[] buf = new char[len + 2 * dimensions];
        basename.getChars(0, len, buf, 0);
        while (dimensions > 0) {
            buf[len++] = '[';
            buf[len++] = ']';
            dimensions--;
        }
        return new String(buf, 0, len);
    }

    public static String toPathName(ReferencePrefix ref) {
        if (ref instanceof NameReference) {
            int dim = (ref instanceof TypeReference) ? ((TypeReference) ref).getDimensions() : 0;
            int length = ((NameReference) ref).getName().length() + 2 * dim;
            ReferencePrefix rp = ref;
            while (rp instanceof ReferenceSuffix) {
                ReferencePrefix rrp = ((ReferenceSuffix) rp).getReferencePrefix();
                if (rrp == null)
                    break;
                rp = rrp;
                length += ((NameReference) rp).getName().length() + 1;
            }
            char[] buf = new char[length];
            int i = 0;
            while (rp != ref) {
                String str = ((NameReference) rp).getName();
                int j = str.length();
                str.getChars(0, j, buf, i);
                i += j;
                buf[i++] = '.';
                rp = (ReferencePrefix) rp.getReferenceSuffix();
            }
            String name = ((NameReference) rp).getName();
            int len = name.length();
            name.getChars(0, len, buf, i);
            i += len;
            while (dim > 0) {
                buf[i++] = '[';
                buf[i++] = ']';
                dim--;
            }
            return new String(buf, 0, length);
        }
        return "";
    }

    public static String toPathName(ReferencePrefix ref, String suffix) {
        if (suffix == null)
            return toPathName(ref);
        int slength = suffix.length();
        if (slength == 0)
            return toPathName(ref);
        if (ref instanceof NameReference) {
            int length = ((NameReference) ref).getName().length() + 1 + slength;
            ReferencePrefix rp = ref;
            while (rp instanceof ReferenceSuffix) {
                ReferencePrefix rrp = ((ReferenceSuffix) rp).getReferencePrefix();
                if (rrp == null)
                    break;
                rp = rrp;
                length += ((NameReference) rp).getName().length() + 1;
            }
            char[] buf = new char[length];
            int i = 0;
            while (rp != ref) {
                String str = ((NameReference) rp).getName();
                int j = str.length();
                str.getChars(0, j, buf, i);
                i += j;
                buf[i++] = '.';
                rp = (ReferencePrefix) rp.getReferenceSuffix();
            }
            String name = ((NameReference) rp).getName();
            int len = name.length();
            name.getChars(0, len, buf, i);
            i += len;
            buf[i++] = '.';
            suffix.getChars(0, slength, buf, i);
            return new String(buf, 0, length);
        }
        return "";
    }

    public static String getPackageName(CompilationUnit cu) {
        PackageSpecification spec = cu.getPackageSpecification();
        if (spec == null)
            return "";
        PackageReference pref = spec.getPackageReference();
        if (pref == null || pref.getName() == null)
            return "";
        return toPathName(pref);
    }

    public static String toCanonicalName(CompilationUnit cu) {
        String name;
        Debug.assertNonnull(cu);
        TypeDeclaration m = cu.getPrimaryTypeDeclaration();
        if (m == null || (!m.isPublic() && cu.getDataLocation() != null)) {
            String possibleFileName, dataLocStr = cu.getDataLocation().toString();
            int lastDot = dataLocStr.lastIndexOf('.');
            int lastSlash = Math.max(dataLocStr.lastIndexOf('/'), dataLocStr.lastIndexOf('\\'));
            if (lastDot >= lastSlash) {
                possibleFileName = dataLocStr.substring(lastSlash + 1, lastDot);
            } else {
                possibleFileName = dataLocStr.substring(lastSlash + 1);
            }
            name = possibleFileName;
        } else {
            name = m.getName();
        }
        String pname = getPackageName(cu);
        if (pname.length() == 0)
            return name;
        return dot(pname, name);
    }

    public static String toCanonicalFilename(CompilationUnit cu) {
        return dot(makeFilename(toCanonicalName(cu)), "java");
    }

    public static String getFullName(ClassTypeContainer ct, String suffix) {
        StringBuffer buffer = new StringBuffer();
        addName(buffer, ct);
        if (suffix != null && suffix.length() > 0) {
            if (buffer.length() > 0)
                buffer.append('.');
            buffer.append(suffix);
        }
        return buffer.toString();
    }

    public static String getFullName(ClassTypeContainer ct) {
        StringBuffer buffer = new StringBuffer();
        addName(buffer, ct);
        return buffer.toString();
    }

    public static String getFullName(Field f) {
        StringBuffer buffer = new StringBuffer();
        addName(buffer, f.getContainingClassType());
        buffer.append('.');
        buffer.append(f.getName());
        return buffer.toString();
    }

    private static boolean addName(StringBuffer buffer, ClassTypeContainer c) {
        ClassTypeContainer container = c.getContainer();
        if (container != null)
            if (container instanceof recoder.abstraction.Method && c instanceof recoder.abstraction.ClassType) {
                int id = System.identityHashCode(container);
                container = container.getContainer();
                if (container != null) {
                    addName(buffer, container);
                    buffer.append('.');
                }
                buffer.append(id);
                buffer.append('.');
            } else if (addName(buffer, container)) {
                buffer.append('.');
            }
        String name = c.getName();
        if (name == null)
            name = String.valueOf(System.identityHashCode(c));
        if (name.length() > 0) {
            buffer.append(name);
            return true;
        }
        return false;
    }

    public static boolean isKeyword(String name) {
        return KEYWORDS.contains(name);
    }
}
