package recoder.kit;

import recoder.ProgramFactory;
import recoder.abstraction.ClassType;
import recoder.abstraction.Member;
import recoder.bytecode.AccessFlags;
import recoder.java.Declaration;
import recoder.java.ProgramElement;
import recoder.java.declaration.DeclarationSpecifier;
import recoder.java.declaration.MemberDeclaration;
import recoder.java.declaration.Modifier;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.modifier.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.ChangeHistory;
import recoder.service.SourceInfo;
import recoder.util.Debug;

public class ModifierKit implements AccessFlags {
    public static final int PACKAGE = 512;

    public static Modifier createModifier(ProgramFactory f, int code) {
        Debug.assertNonnull(f);
        switch (code) {
            case 512:
                return null;
            case 1:
                return f.createPublic();
            case 4:
                return f.createProtected();
            case 2:
                return f.createPrivate();
            case 8:
                return f.createStatic();
            case 16:
                return f.createFinal();
            case 1024:
                return f.createAbstract();
            case 32:
                return f.createSynchronized();
            case 128:
                return f.createTransient();
            case 2048:
                return f.createStrictFp();
            case 64:
                return f.createVolatile();
            case 256:
                return f.createNative();
        }
        throw new IllegalArgumentException("Unsupported modifier code " + code);
    }

    public static int getCode(Modifier m) {
        if (m == null)
            return 512;
        if (m instanceof VisibilityModifier) {
            if (m instanceof Public)
                return 1;
            if (m instanceof Protected)
                return 4;
            if (m instanceof Private)
                return 2;
        } else {
            if (m instanceof Static)
                return 8;
            if (m instanceof Final)
                return 16;
            if (m instanceof Abstract)
                return 1024;
            if (m instanceof Synchronized)
                return 32;
            if (m instanceof Transient)
                return 128;
            if (m instanceof StrictFp)
                return 2048;
            if (m instanceof Volatile)
                return 64;
            if (m instanceof Native)
                return 256;
        }
        throw new IllegalArgumentException("Unknown Modifier " + m.getClass().getName());
    }

    public static VisibilityModifier getVisibilityModifier(Declaration decl) {
        Debug.assertNonnull(decl);
        ASTList<DeclarationSpecifier> aSTList = decl.getDeclarationSpecifiers();
        if (aSTList == null)
            return null;
        for (int i = 0; i < aSTList.size(); i++) {
            DeclarationSpecifier res = aSTList.get(i);
            if (res instanceof VisibilityModifier)
                return (VisibilityModifier) res;
        }
        return null;
    }

    private static boolean containsModifier(Declaration decl, Class mod) {
        Debug.assertNonnull(decl, mod);
        ASTList<DeclarationSpecifier> aSTList = decl.getDeclarationSpecifiers();
        if (aSTList == null)
            return false;
        for (int i = 0; i < aSTList.size(); i++) {
            DeclarationSpecifier res = aSTList.get(i);
            if (mod.isInstance(res))
                return true;
        }
        return false;
    }

    private static DeclarationSpecifier modify(ChangeHistory ch, int code, Declaration decl) {
        ASTArrayList aSTArrayList;
        VisibilityModifier visibilityModifier6;
        Public public_;
        VisibilityModifier visibilityModifier5;
        Protected protected_;
        VisibilityModifier visibilityModifier4;
        Private private_;
        VisibilityModifier visibilityModifier3;
        Static static_;
        VisibilityModifier visibilityModifier2;
        Final final_;
        VisibilityModifier visibilityModifier1;
        Abstract abstract_;
        Synchronized synchronized_;
        Transient transient_;
        StrictFp strictFp;
        Volatile volatile_;
        Native native_;
        Debug.assertNonnull(decl);
        ASTList<DeclarationSpecifier> mods = decl.getDeclarationSpecifiers();
        ProgramFactory fact = decl.getFactory();
        int insertPos = 0;
        switch (code) {
            case 512:
                if (code == 512) {
                    VisibilityModifier visibilityModifier = getVisibilityModifier(decl);
                    if (visibilityModifier != null)
                        MiscKit.remove(ch, visibilityModifier);
                    return null;
                }
            case 1:
                visibilityModifier6 = getVisibilityModifier(decl);
                if (visibilityModifier6 instanceof Public)
                    return null;
                if (visibilityModifier6 != null)
                    MiscKit.remove(ch, visibilityModifier6);
                if (mods == null)
                    decl.setDeclarationSpecifiers(aSTArrayList = new ASTArrayList());
                public_ = fact.createPublic();
                insertPos = 0;
                break;
            case 4:
                visibilityModifier5 = getVisibilityModifier(decl);
                if (visibilityModifier5 instanceof Protected)
                    return null;
                if (visibilityModifier5 != null)
                    MiscKit.remove(ch, visibilityModifier5);
                if (aSTArrayList == null)
                    decl.setDeclarationSpecifiers(aSTArrayList = new ASTArrayList());
                protected_ = fact.createProtected();
                insertPos = 0;
                break;
            case 2:
                visibilityModifier4 = getVisibilityModifier(decl);
                if (visibilityModifier4 instanceof Private)
                    return null;
                if (visibilityModifier4 != null)
                    MiscKit.remove(ch, visibilityModifier4);
                if (aSTArrayList == null)
                    decl.setDeclarationSpecifiers(aSTArrayList = new ASTArrayList());
                private_ = fact.createPrivate();
                insertPos = 0;
                break;
            case 8:
                if (containsModifier(decl, Static.class))
                    return null;
                visibilityModifier3 = getVisibilityModifier(decl);
                insertPos = (visibilityModifier3 == null) ? 0 : 1;
                static_ = fact.createStatic();
                break;
            case 16:
                if (containsModifier(decl, Final.class))
                    return null;
                visibilityModifier2 = getVisibilityModifier(decl);
                insertPos = (visibilityModifier2 == null) ? 0 : 1;
                if (containsModifier(decl, Static.class))
                    insertPos++;
                final_ = fact.createFinal();
                break;
            case 1024:
                if (containsModifier(decl, Abstract.class))
                    return null;
                visibilityModifier1 = getVisibilityModifier(decl);
                insertPos = (visibilityModifier1 == null) ? 0 : 1;
                abstract_ = fact.createAbstract();
                break;
            case 32:
                if (containsModifier(decl, Synchronized.class))
                    return null;
                insertPos = (aSTArrayList == null) ? 0 : aSTArrayList.size();
                synchronized_ = fact.createSynchronized();
                break;
            case 128:
                if (containsModifier(decl, Transient.class))
                    return null;
                insertPos = (aSTArrayList == null) ? 0 : aSTArrayList.size();
                transient_ = fact.createTransient();
                break;
            case 2048:
                if (containsModifier(decl, StrictFp.class))
                    return null;
                insertPos = (aSTArrayList == null) ? 0 : aSTArrayList.size();
                strictFp = fact.createStrictFp();
                break;
            case 64:
                if (containsModifier(decl, Volatile.class))
                    return null;
                insertPos = (aSTArrayList == null) ? 0 : aSTArrayList.size();
                volatile_ = fact.createVolatile();
                break;
            case 256:
                if (containsModifier(decl, Native.class))
                    return null;
                insertPos = (aSTArrayList == null) ? 0 : aSTArrayList.size();
                native_ = fact.createNative();
                break;
            default:
                throw new IllegalArgumentException("Unsupported modifier code " + code);
        }
        aSTArrayList.add(insertPos, native_);
        native_.setParent(decl);
        if (ch != null)
            ch.attached(native_);
        return native_;
    }

    public static boolean makeVisible(ChangeHistory ch, SourceInfo si, MemberDeclaration mdecl, ClassType ct) {
        int minimumNeeded;
        Debug.assertNonnull(si, mdecl, ct);
        Debug.assertBoolean(mdecl instanceof Member);
        if (si.isVisibleFor((Member) mdecl, ct))
            return true;
        TypeDeclaration mt = mdecl.getMemberParent();
        if (mt == ct) {
            minimumNeeded = 2;
        } else if (mt.getPackage() == ct.getPackage()) {
            minimumNeeded = 512;
        } else if (si.isSubtype(mt, ct)) {
            minimumNeeded = 4;
        } else {
            minimumNeeded = 1;
        }
        modify(ch, minimumNeeded, mdecl);
        return false;
    }
}
