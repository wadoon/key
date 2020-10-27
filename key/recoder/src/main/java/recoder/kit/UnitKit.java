package recoder.kit;

import recoder.ProgramFactory;
import recoder.abstraction.ArrayType;
import recoder.abstraction.ClassType;
import recoder.abstraction.Package;
import recoder.abstraction.Type;
import recoder.convenience.Format;
import recoder.convenience.Naming;
import recoder.convenience.TreeWalker;
import recoder.java.*;
import recoder.java.reference.MethodReference;
import recoder.java.reference.PackageReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;
import recoder.service.ChangeHistory;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.SourceInfo;
import recoder.util.Debug;
import recoder.util.Order;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class UnitKit {
    public static CompilationUnit getCompilationUnit(ProgramElement p) {
        while (p != null) {
            if (p instanceof CompilationUnit)
                return (CompilationUnit) p;
            NonTerminalProgramElement nonTerminalProgramElement = p.getASTParent();
        }
        return null;
    }

    private static ClassType getNecessaryImportedType(CrossReferenceSourceInfo xi, Import imp) {
        if (imp.isMultiImport())
            return null;
        TypeReference tr = imp.getTypeReference();
        ClassType ct = (ClassType) xi.getType(tr);
        if (ct == null)
            throw new RuntimeException("No type found for " + Format.toString("%c \"%s\" @%p in %f", tr));
        if (TypeKit.getReferences(xi, ct, imp.getASTParent(), false).size() > 1)
            return ct;
        return null;
    }

    private static boolean isNecessaryMultiTypeImport(CrossReferenceSourceInfo xrsi, Import imp, Set coveredTypes) {
        List<? extends ClassType> types;
        if (!imp.isMultiImport())
            return false;
        if (imp.isStaticImport())
            return true;
        TypeReference typeReference = imp.getTypeReference();
        CompilationUnit cu = imp.getParent();
        if (typeReference instanceof PackageReference) {
            types = xrsi.getPackage((PackageReference) typeReference).getTypes();
        } else {
            types = ((ClassType) xrsi.getType(typeReference)).getTypes();
        }
        boolean result = false;
        for (int j = types.size() - 1; j >= 0 && !result; j--) {
            ClassType ct = types.get(j);
            if (!coveredTypes.contains(ct)) {
                List<TypeReference> refs = TypeKit.getReferences(xrsi, ct, cu, false);
                for (int k = refs.size() - 1; k >= 0; k--) {
                    if (refs.get(k).getASTParent().getASTParent() == cu)
                        refs.remove(k);
                }
                result = !refs.isEmpty();
            }
        }
        return result;
    }

    public static List<Import> getUnnecessaryImports(CrossReferenceSourceInfo xrsi, CompilationUnit cu) {
        Debug.assertNonnull(xrsi, cu);
        ASTList<Import> aSTList = cu.getImports();
        if (aSTList == null || aSTList.isEmpty())
            return new ArrayList<Import>(0);
        List<Import> removalList = new ArrayList<Import>();
        Set<ClassType> coveredTypes = new HashSet<ClassType>();
        int i, s;
        for (i = 0, s = aSTList.size(); i < s; i++) {
            Import imp = aSTList.get(i);
            if (!imp.isStaticImport() &&
                    !imp.isMultiImport()) {
                ClassType ct = getNecessaryImportedType(xrsi, imp);
                if (ct != null) {
                    coveredTypes.add(ct);
                } else {
                    removalList.add(imp);
                }
            }
        }
        for (i = 0, s = aSTList.size(); i < s; i++) {
            Import imp = aSTList.get(i);
            if (!imp.isStaticImport() &&
                    imp.isMultiImport() && !isNecessaryMultiTypeImport(xrsi, imp, coveredTypes))
                removalList.add(imp);
        }
        return removalList;
    }

    public static void removeUnusedImports(ChangeHistory ch, CrossReferenceSourceInfo xrsi, CompilationUnit cu) {
        Debug.assertNonnull(ch);
        List<Import> removalList = getUnnecessaryImports(xrsi, cu);
        for (int i = removalList.size() - 1; i >= 0; i--)
            MiscKit.remove(ch, removalList.get(i));
    }

    public static void normalizeImports(ChangeHistory ch, CrossReferenceSourceInfo xrsi, CompilationUnit cu, boolean removeMultiTypeImports, boolean removeSingleTypeImports, boolean addJavaLangImports, boolean addDefaultPackageImports) {
        Debug.assertNonnull(xrsi, cu);
        Set<ClassType> importTypes = new HashSet<ClassType>();
        Package unitPackage = cu.getPrimaryTypeDeclaration().getPackage();
        TreeWalker tw = new TreeWalker(cu);
        for (int i = cu.getTypeDeclarationCount() - 1; i >= 0; i--) {
            tw.reset(cu.getTypeDeclarationAt(i));
            while (tw.next(TypeReference.class)) {
                TypeReference tr = (TypeReference) tw.getProgramElement();
                Type type = xrsi.getType(tr);
                while (type instanceof ArrayType)
                    type = ((ArrayType) type).getBaseType();
                if (type instanceof ClassType && (!(type instanceof recoder.java.declaration.TypeDeclaration) || !MiscKit.contains(cu, (ProgramElement) type)) && (addDefaultPackageImports || ((ClassType) type).getPackage() != unitPackage) && (addJavaLangImports || !type.getFullName().startsWith("java.lang.")))
                    importTypes.add((ClassType) type);
            }
        }
        ASTList<Import> aSTList = cu.getImports();
        int ilsize = (aSTList == null) ? 0 : aSTList.size();
        ClassType[] classTypes = new ClassType[ilsize];
        Set<ClassType> importedTypes = new HashSet<ClassType>();
        for (int j = ilsize - 1; j >= 0; j--) {
            Import imp = aSTList.get(j);
            if (!imp.isMultiImport()) {
                TypeReference tr = imp.getTypeReference();
                ClassType ct = (ClassType) xrsi.getType(tr);
                classTypes[j] = ct;
                importedTypes.add(ct);
            }
        }
        Set<ClassType> commonTypes = new HashSet<ClassType>(importTypes.size());
        commonTypes.addAll(importTypes);
        commonTypes.retainAll(importedTypes);
        importTypes.removeAll(commonTypes);
        importedTypes.removeAll(commonTypes);
        for (int k = ilsize - 1; k >= 0; k--) {
            Import imp = aSTList.get(k);
            if (!imp.isStaticImport() && ((
                    imp.isMultiImport() && removeMultiTypeImports) || (!imp.isMultiImport() && removeSingleTypeImports && importedTypes.contains(classTypes[k]))))
                MiscKit.remove(ch, imp);
        }
        for (ClassType ct : importedTypes)
            appendImport(ch, cu, ct);
    }

    public static Import appendImport(ChangeHistory ch, CompilationUnit cu, ClassType ct) {
        return appendImport(ch, cu, ct.getFullName());
    }

    public static Import appendImport(ChangeHistory ch, CompilationUnit cu, String typeName) {
        Debug.assertNonnull(cu, typeName);
        ProgramFactory factory = cu.getFactory();
        TypeReference ref = TypeKit.createTypeReference(factory, typeName);
        Import newImport = factory.createImport(ref, false);
        newImport.makeAllParentRolesValid();
        MiscKit.append(ch, cu, newImport);
        return newImport;
    }

    public static Import ensureImport(ChangeHistory ch, SourceInfo si, String typeName, ProgramElement context) {
        Debug.assertNonnull(si, typeName, context);
        Debug.assertBoolean((typeName.length() > 0));
        if (si.getType(typeName, context) != null)
            return null;
        return appendImport(ch, MiscKit.getParentCompilationUnit(context), typeName);
    }

    public static void ensureImports(ChangeHistory ch, SourceInfo si, ProgramElement root) {
        Debug.assertNonnull(si, root);
        CompilationUnit cu = MiscKit.getParentCompilationUnit(root);
        TreeWalker tw = new TreeWalker(root);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof TypeReference) {
                String name = Naming.toPathName((ReferencePrefix) pe);
                while (name.endsWith("]"))
                    name = name.substring(0, name.length() - 2);
                Type type = si.getType(name, pe);
                if (type == null)
                    ensureImport(ch, si, name, cu);
            }
        }
    }

    public static void sortImports(ChangeHistory ch, CompilationUnit cu) {
        Debug.assertNonnull(cu);
        ASTList<Import> aSTList = cu.getImports();
        if (aSTList == null)
            return;
        String[] names = new String[aSTList.size()];
        int i;
        for (i = 0; i < aSTList.size(); i++) {
            Import imp = aSTList.get(i);
            if (imp.isStaticImport() && !imp.isMultiImport()) {
                MethodReference ref = (MethodReference) imp.getReference();
                names[i] = Naming.toPathName(ref.getReferencePrefix(), "." + ref.getName());
            } else {
                names[i] = Naming.toPathName(imp.getReference());
            }
        }
        for (i = 1; i < names.length; i++) {
            String x = names[i];
            int k = i - 1;
            while (k >= 0 && Order.LEXICAL.greater(names[k], x)) {
                names[k + 1] = names[k];
                k--;
            }
            names[k + 1] = x;
            if (k + 1 != i) {
                Import oldImp = aSTList.get(i);
                aSTList.remove(i);
                aSTList.add(k + 1, oldImp);
                if (ch != null) {
                    ch.detached(oldImp, cu, i);
                    ch.attached(oldImp);
                }
            }
        }
        String prefix = null;
        for (int j = 0; j < names.length; j++) {
            String name = names[j];
            int dot = name.indexOf('.');
            String newPrefix = (dot >= 0) ? name.substring(0, dot) : name;
            if (j > 0 && !prefix.equals(newPrefix)) {
                Import imp = aSTList.get(j);
                SourceElement.Position pos = imp.getFirstElement().getRelativePosition();
                if (pos.getLine() == 0) {
                    pos.setLine(1);
                    imp.getFirstElement().setRelativePosition(pos);
                }
            }
            prefix = newPrefix;
        }
    }
}
