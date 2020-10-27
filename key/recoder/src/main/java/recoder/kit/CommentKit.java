package recoder.kit;

import recoder.ProgramFactory;
import recoder.abstraction.ClassType;
import recoder.java.DocComment;
import recoder.java.ProgramElement;
import recoder.java.declaration.*;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;
import recoder.service.NameInfo;
import recoder.service.SourceInfo;
import recoder.util.Debug;

public class CommentKit {
    public static DocComment createDoc(MethodDeclaration method, boolean dummy) {
        Debug.assertNonnull(method);
        StringBuffer text = new StringBuffer("/**\n");
        if (dummy) {
            text.append("  ");
            text.append(guessDocumentation(method.getName(), true));
            text.append("\n");
        }
        int c = method.getParameterDeclarationCount();
        for (int i = 0; i < c; i++) {
            ParameterDeclaration param = method.getParameterDeclarationAt(i);
            text.append("  @param " + param.getVariables().get(0).getName() + ' ');
            if (dummy)
                text.append(guessDocumentation(param.getTypeReference(), false));
            text.append('\n');
        }
        TypeReference ret = method.getTypeReference();
        if (ret != null && !"void".equals(ret.getName())) {
            text.append("  @return ");
            if (dummy)
                text.append(guessDocumentation(ret, true));
            text.append('\n');
        }
        Throws th = method.getThrown();
        if (th != null) {
            ASTList<TypeReference> aSTList = th.getExceptions();
            for (int j = 0; j < aSTList.size(); j++) {
                TypeReference tr = aSTList.get(j);
                text.append("  @exception " + tr.getName());
                if (dummy)
                    text.append(" occasionally thrown.\n");
            }
        }
        text.append("*/");
        return method.getFactory().createDocComment(text.toString());
    }

    public static DocComment createDoc(FieldDeclaration field, boolean dummy) {
        Debug.assertNonnull(field);
        ProgramFactory factory = field.getFactory();
        if (dummy) {
            String name = field.getVariables().get(0).getName();
            return factory.createDocComment("/**\n  " + guessDocumentation(name, true) + "\n*/");
        }
        return factory.createDocComment("/**\n  \n*/");
    }

    public static DocComment createDoc(SourceInfo si, NameInfo ni, FieldDeclaration field, boolean dummy) {
        boolean isSerial;
        Debug.assertNonnull(field);
        TypeDeclaration td = MiscKit.getParentTypeDeclaration(field);
        if (td instanceof recoder.java.declaration.ClassDeclaration) {
            isSerial = si.isSubtype(td, ni.getJavaIoSerializable());
        } else {
            isSerial = false;
        }
        ProgramFactory factory = field.getFactory();
        if (dummy) {
            String name = field.getVariables().get(0).getName();
            return factory.createDocComment("/**\n  " + guessDocumentation(name, true) + (isSerial ? "\n  @serial" : "") + "\n*/");
        }
        return factory.createDocComment("/**\n  " + (isSerial ? "\n  @serial" : "") + "n*/");
    }

    public static DocComment createDoc(TypeDeclaration type, boolean dummy) {
        Debug.assertNonnull(type);
        ProgramFactory factory = type.getFactory();
        if (dummy) {
            String name = type.getName();
            return factory.createDocComment("/**\n  " + guessDocumentation(name, true) + "\n  @author " + "\n*/");
        }
        return factory.createDocComment("/**\n  \n*/");
    }

    static String guessDocumentation(TypeReference tr, boolean returned) {
        String tn = tr.getName();
        if (tr.getDimensions() == 0 && (
                tn.equals("int") || tn.equals("boolean") || tn.equals("short") || tn.equals("long") || tn.equals("byte") || tn.equals("char") || tn.equals("float") || tn.equals("double")))
            tn = tn + " value";
        String ty = guessDocumentation(tn, false);
        switch (tr.getDimensions()) {
            case 0:
                if (returned)
                    return "the " + ty;
                if ("aeiouAEIOU".indexOf(ty.charAt(0)) >= 0)
                    return "an " + ty;
                return "a " + ty;
            case 1:
                return (returned ? "the" : "an") + " array of " + ty;
            case 2:
                return (returned ? "the" : "a") + " matrix of " + ty;
        }
        return (returned ? "the" : "a") + " multi-dimensional array of " + ty;
    }

    static String guessDocumentation(String name, boolean capital) {
        int len = name.length();
        StringBuffer res = new StringBuffer(len + 6);
        for (int i = 0; i < len; i++) {
            char ch = name.charAt(i);
            if (Character.isUpperCase(ch)) {
                if (i < len - 1 && Character.isUpperCase(name.charAt(i + 1))) {
                    if (i > 0 && !Character.isUpperCase(name.charAt(i - 1)))
                        res.append(' ');
                    res.append(ch);
                } else {
                    if (i > 0)
                        res.append(' ');
                    res.append(Character.toLowerCase(ch));
                }
            } else {
                res.append(ch);
            }
        }
        if (capital)
            res.setCharAt(0, Character.toUpperCase(res.charAt(0)));
        res.append('.');
        return res.toString();
    }
}
