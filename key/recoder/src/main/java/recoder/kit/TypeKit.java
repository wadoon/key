package recoder.kit;

import recoder.ProgramFactory;
import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.convenience.TreeWalker;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.VisibilityModifier;
import recoder.java.reference.FieldReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.*;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.List;

public class TypeKit {
    public static TypeReference createTypeReference(ConstructorDeclaration decl) {
        ProgramFactory f = decl.getFactory();
        TypeReference result = f.createTypeReference(f.createIdentifier(decl.getName()));
        result.makeAllParentRolesValid();
        return result;
    }

    public static TypeReference createTypeReference(ProgramFactory f, String qualifiedName) {
        return MiscKit.createUncollatedReferenceQualifier(f, qualifiedName).toTypeReference();
    }

    public static ASTList<TypeArgumentDeclaration> makeTypeArgRef(ProgramFactory f, List<? extends TypeArgument> tas) {
        ASTArrayList aSTArrayList = new ASTArrayList(tas.size());
        for (TypeArgument ta : tas) {
            TypeReference tr = createTypeReference(f, ta.getTypeName());
            if (ta.getTypeArguments() != null)
                tr.setTypeArguments(makeTypeArgRef(f, ta.getTypeArguments()));
            aSTArrayList.add(new TypeArgumentDeclaration(tr, ta.getWildcardMode()));
        }
        return (ASTList<TypeArgumentDeclaration>) aSTArrayList;
    }

    public static TypeReference createTypeReference(ProgramFactory f, Type t, boolean addTypeArgs) {
        TypeReference result = null;
        if (t instanceof recoder.abstraction.PrimitiveType) {
            result = f.createTypeReference(f.createIdentifier(t.getName()));
        } else if (t instanceof ParameterizedType) {
            ParameterizedType pt = (ParameterizedType) t;
            result = createTypeReference(f, pt.getGenericType());
            if (addTypeArgs)
                result.setTypeArguments(makeTypeArgRef(f, pt.getTypeArgs()));
        } else if (t instanceof ClassType) {
            result = f.createTypeReference(f.createIdentifier(t.getName()));
            ClassTypeContainer ctc = ((ClassType) t).getContainer();
            if (ctc instanceof Package) {
                result.setReferencePrefix(PackageKit.createPackageReference(f, (Package) ctc));
            } else if (ctc instanceof ClassType) {
                result.setReferencePrefix(createTypeReference(f, (Type) ctc));
            }
        } else if (t instanceof ArrayType) {
            result = createTypeReference(f, ((ArrayType) t).getBaseType());
            result.setDimensions(result.getDimensions() + 1);
        }
        result.makeParentRoleValid();
        return result;
    }

    public static TypeReference createTypeReference(ProgramFactory f, Type t) {
        return createTypeReference(f, t, false);
    }

    public static TypeReference createTypeReference(SourceInfo si, Type t, ProgramElement context) {
        TypeReference result = null;
        ProgramFactory f = context.getFactory();
        if (t instanceof recoder.abstraction.PrimitiveType) {
            result = f.createTypeReference(f.createIdentifier(t.getName()));
        } else if (t instanceof ClassType) {
            result = f.createTypeReference(f.createIdentifier(t.getName()));
            ClassTypeContainer ctc = ((ClassType) t).getContainer();
            if (ctc != null && si.getType(t.getName(), context) != t)
                if (ctc instanceof Package) {
                    result.setReferencePrefix(PackageKit.createPackageReference(f, (Package) ctc));
                } else if (ctc instanceof ClassType) {
                    result.setReferencePrefix(createTypeReference(f, (Type) ctc));
                }
        } else if (t instanceof ArrayType) {
            result = createTypeReference(si, ((ArrayType) t).getBaseType(), context);
            result.setDimensions(result.getDimensions() + 1);
        }
        result.makeAllParentRolesValid();
        return result;
    }

    public static InterfaceDeclaration createAbstractSuperClass(NameInfo ni, ClassDeclaration cdecl, String abstractsupername) throws NameClashException {
        String message = "Sorry, only public classes which are neither interfaces nor enums can be transformed.";
        Debug.assertBoolean((cdecl.isPublic() && !cdecl.isInterface() && !cdecl.isEnumType()), message);
        if (ni.getType(abstractsupername) != null)
            throw new NameClashException("Error: Name " + abstractsupername + "is already declared.");
        ProgramFactory pf = cdecl.getFactory();
        ASTArrayList aSTArrayList = new ASTArrayList(1);
        ASTList<MemberDeclaration> cmems = cdecl.getMembers();
        if (cmems != null) {
            for (int i = 0, s = cmems.size(); i < s; i++) {
                MemberDeclaration cmemd = cmems.get(i);
                if (cmemd.isPublic())
                    if (cmemd instanceof FieldDeclaration) {
                        if (((FieldDeclaration) cmemd).isFinal() && cmemd.isStatic()) {
                            FieldDeclaration d = (FieldDeclaration) cmemd.deepClone();
                            ASTList<FieldSpecification> aSTList = d.getFieldSpecifications();
                            for (int j = 0, z = aSTList.size(); j < z; j++) {
                                if (aSTList.get(j).getInitializer() == null) {
                                    aSTList.remove(j);
                                    j--;
                                    z--;
                                }
                            }
                            if (aSTList.size() > 0)
                                aSTArrayList.add(d);
                        }
                    } else if (cmemd instanceof MethodDeclaration) {
                        MethodDeclaration md = (MethodDeclaration) cmemd;
                        if (!md.isStatic() && md.isPublic() && !(md instanceof ConstructorDeclaration))
                            aSTArrayList.add(MethodKit.createAbstractMethodDeclaration(md, true));
                    } else if (cmemd instanceof TypeDeclaration) {
                        aSTArrayList.add(cmemd.deepClone());
                    }
            }
            if (!aSTArrayList.isEmpty()) {
                ASTArrayList aSTArrayList1;
                Identifier iid = pf.createIdentifier(abstractsupername);
                VisibilityModifier visibilityModifier = cdecl.getVisibilityModifier();
                ASTList<DeclarationSpecifier> imods = null;
                if (visibilityModifier != null) {
                    aSTArrayList1 = new ASTArrayList(1);
                    aSTArrayList1.add(visibilityModifier.deepClone());
                }
                InterfaceDeclaration idecl = pf.createInterfaceDeclaration(aSTArrayList1, iid, null, aSTArrayList);
                ASTArrayList aSTArrayList2 = new ASTArrayList(1);
                TypeReference iref = pf.createTypeReference(iid);
                Implements impl = cdecl.getImplementedTypes();
                if (impl == null) {
                    impl = new Implements(iref);
                } else {
                    ASTList aSTList = impl.getSupertypes();
                    aSTList.add(iref);
                    impl.setSupertypes(aSTList);
                }
                cdecl.setImplementedTypes(impl);
                return idecl;
            }
            return null;
        }
        return null;
    }

    public static InterfaceDeclaration createInterfaceDeclaration(ClassDeclaration decl) {
        ProgramFactory factory = decl.getFactory();
        InterfaceDeclaration res = factory.createInterfaceDeclaration();
        res.setIdentifier(factory.createIdentifier("Abstract" + decl.getName()));
        VisibilityModifier visibilityModifier = decl.getVisibilityModifier();
        if (visibilityModifier != null) {
            ASTArrayList aSTArrayList1 = new ASTArrayList(1);
            aSTArrayList1.add(visibilityModifier.deepClone());
            res.setDeclarationSpecifiers(aSTArrayList1);
        }
        ASTArrayList aSTArrayList = new ASTArrayList();
        res.setMembers(aSTArrayList);
        ASTList<MemberDeclaration> aSTList = decl.getMembers();
        if (aSTList == null)
            return res;
        for (int i = 0, s = aSTList.size(); i < s; i++) {
            MemberDeclaration cmemd = aSTList.get(i);
            if (cmemd.isPublic())
                if (cmemd instanceof FieldDeclaration) {
                    if (((FieldDeclaration) cmemd).isFinal() && cmemd.isStatic()) {
                        FieldDeclaration d = (FieldDeclaration) cmemd.deepClone();
                        ASTList<FieldSpecification> aSTList1 = d.getFieldSpecifications();
                        for (int j = 0, z = aSTList1.size(); j < z; j++) {
                            if (aSTList1.get(j).getInitializer() == null) {
                                aSTList1.remove(j);
                                j--;
                                z--;
                            }
                        }
                        if (aSTList1.size() > 0)
                            aSTArrayList.add(d);
                    }
                } else if (cmemd instanceof MethodDeclaration) {
                    if (!(cmemd instanceof ConstructorDeclaration) && !cmemd.isStatic())
                        aSTArrayList.add(MethodKit.createAbstractMethodDeclaration((MethodDeclaration) cmemd, true));
                } else if (cmemd instanceof TypeDeclaration) {
                    aSTArrayList.add(cmemd.deepClone());
                }
        }
        return res;
    }

    public static ClassDeclaration createAdapterClass(String adapterName, ClassDeclaration classDecl) {
        ProgramFactory factory = classDecl.getFactory();
        FieldReference fieldReference = new FieldReference(factory.createIdentifier("delegationObject" + classDecl.getName()));
        ClassDeclaration adapterClass = factory.createClassDeclaration(new ASTArrayList(), factory.createIdentifier(adapterName), factory.createExtends(), factory.createImplements(), new ASTArrayList());
        for (int i2 = 0; i2 < classDecl.getMembers().size(); i2++) {
            MemberDeclaration member = classDecl.getMembers().get(i2);
            if (member instanceof MethodDeclaration) {
                MethodDeclaration method = (MethodDeclaration) member;
                if (method.isPublic()) {
                    Debug.info(2, "adapting public method " + method.getName());
                    MethodDeclaration clone = MethodKit.createAdapterMethod(fieldReference, method);
                    if (clone != null)
                        adapterClass.getMembers().add(clone);
                }
            }
        }
        return adapterClass;
    }

    public static boolean rename(ChangeHistory ch, CrossReferenceSourceInfo xr, NameInfo ni, TypeDeclaration type, String newName) {
        Debug.assertNonnull(xr, ni, type, newName);
        Debug.assertNonnull(type.getName());
        if (!newName.equals(type.getName())) {
            List<TypeReference> refs = new ArrayList<TypeReference>();
            refs.addAll(xr.getReferences(type));
            List<? extends Constructor> cons = type.getConstructors();
            ArrayType arrayType = ni.getArrayType(type);
            while (arrayType != null) {
                refs.addAll(xr.getReferences(arrayType));
                arrayType = ni.getArrayType(arrayType);
            }
            MiscKit.rename(ch, type, newName);
            if (cons != null)
                for (int i = cons.size() - 1; i >= 0; i--) {
                    Constructor con = cons.get(i);
                    if (con instanceof ConstructorDeclaration)
                        MiscKit.rename(ch, (NamedProgramElement) con, newName);
                }
            if (refs != null)
                for (int i = refs.size() - 1; i >= 0; i--)
                    MiscKit.rename(ch, refs.get(i), newName);
            return true;
        }
        return false;
    }

    public static List<TypeReference> getInfluencedReferences(CrossReferenceSourceInfo xr, String newTypeName, NonTerminalProgramElement context) {
        Debug.assertNonnull(xr, newTypeName, context);
        ScopeDefiningElement scopeDefiningElement = MiscKit.getScopeDefiningElement(context);
        Type t = xr.getType(newTypeName, scopeDefiningElement);
        if (t == null)
            return new ArrayList<TypeReference>(0);
        List<TypeReference> list = xr.getReferences(t);
        if (list.isEmpty())
            return list;
        List<TypeReference> result = new ArrayList<TypeReference>();
        for (int i = list.size() - 1; i >= 0; i--) {
            TypeReference tr = list.get(i);
            if (MiscKit.contains(scopeDefiningElement, tr))
                result.add(tr);
        }
        return result;
    }

    public static List<TypeReference> getReferences(CrossReferenceSourceInfo xr, Type t, NonTerminalProgramElement root, boolean scanTree) {
        Debug.assertNonnull(xr, t, root);
        List<TypeReference> result = new ArrayList<TypeReference>();
        if (scanTree) {
            TreeWalker tw = new TreeWalker(root);
            while (tw.next(TypeReference.class)) {
                TypeReference tr = (TypeReference) tw.getProgramElement();
                if (xr.getType(tr) == t)
                    result.add(tr);
            }
        } else {
            List<TypeReference> refs = xr.getReferences(t);
            for (int i = 0, s = refs.size(); i < s; i++) {
                TypeReference tr = refs.get(i);
                if (MiscKit.contains(root, tr))
                    result.add(tr);
            }
        }
        return result;
    }

    public static List<Member> getMembers(ClassTypeContainer ctc) {
        List<Member> result = new ArrayList<Member>();
        if (ctc instanceof ClassType) {
            ClassType ct = (ClassType) ctc;
            List<? extends Member> list = ct.getConstructors();
            if (list != null)
                result.addAll(list);
            list = ct.getFields();
            if (list != null)
                result.addAll(list);
            list = ct.getMethods();
            if (list != null)
                result.addAll(list);
        }
        List<? extends Member> mlist = ctc.getTypes();
        if (mlist != null)
            result.addAll(mlist);
        return result;
    }

    public static ClassType getSuperClass(NameInfo ni, ClassType ct) {
        if (!ct.isInterface()) {
            List<? extends ClassType> ctl = ct.getSupertypes();
            for (int i = 0; i < ctl.size(); i++) {
                ct = ctl.get(i);
                if (!ct.isInterface())
                    return ct;
            }
        }
        return ni.getJavaLangObject();
    }

    public static boolean isLessVisible(Member x, Member y) {
        if (x.isPublic())
            return false;
        if (y.isPublic())
            return true;
        if (x.isProtected())
            return false;
        if (y.isProtected())
            return true;
        return (x.isPrivate() && !y.isPrivate());
    }

    public static boolean isCovered(ProgramModelInfo pmi, List<? extends ClassType> x, List<? extends ClassType> y) {
        Debug.assertNonnull(x, y);
        boolean found = true;
        for (int i = x.size() - 1; i >= 0 && found; i--) {
            ClassType ct = x.get(i);
            found = false;
            for (int j = y.size() - 1; j >= 0; j--) {
                if (pmi.isSubtype(ct, y.get(j))) {
                    found = true;
                    break;
                }
            }
        }
        return found;
    }

    public static boolean isValidInterfaceMember(MemberDeclaration member) {
        if (!member.isPublic())
            return false;
        if (member instanceof FieldDeclaration) {
            if (!member.isStatic() || !((FieldDeclaration) member).isFinal())
                return false;
            List<? extends VariableSpecification> vars = ((FieldDeclaration) member).getVariables();
            for (int j = 0, z = vars.size(); j < z; j++) {
                if (vars.get(j).getInitializer() == null)
                    return false;
            }
            return true;
        }
        if (member instanceof MethodDeclaration)
            return (!(member instanceof ConstructorDeclaration) && !member.isStatic() && ((MethodDeclaration) member).getBody() == null);
        return member instanceof TypeDeclaration;
    }

    public static List<? extends ClassType> getCoveredSubtypes(ProgramModelInfo pmi, List<? extends ClassType> list) {
        List<ClassType> copy = new ArrayList<ClassType>();
        copy.addAll(list);
        return removeCoveredSubtypes(pmi, copy);
    }

    public static List<ClassType> removeCoveredSubtypes(ProgramModelInfo pmi, List<ClassType> list) {
        List<ClassType> removed = new ArrayList<ClassType>();
        for (int i = list.size() - 1; i >= 0; i--) {
            ClassType ct = list.get(i);
            for (int j = list.size() - 1; j >= 0; j--) {
                if (j != i) {
                    ClassType ct2 = list.get(j);
                    if (pmi.isSubtype(ct, ct2)) {
                        removed.add(ct);
                        list.remove(i);
                        break;
                    }
                }
            }
        }
        return removed;
    }

    public static List<TypeReference> getRedundantSuperInterfaces(SourceInfo si, TypeDeclaration td) {
        ASTList<TypeReference> aSTList;
        ClassType superclass = null;
        List<TypeReference> superinterfaces = new ArrayList<TypeReference>(0);
        if (td instanceof InterfaceDeclaration) {
            InterfaceDeclaration id = (InterfaceDeclaration) td;
            if (id.getExtendedTypes() != null)
                aSTList = id.getExtendedTypes().getSupertypes();
        } else {
            ClassDeclaration cd = (ClassDeclaration) td;
            if (cd.getImplementedTypes() != null)
                aSTList = cd.getImplementedTypes().getSupertypes();
            if (cd.getExtendedTypes() != null)
                superclass = (ClassType) si.getType(cd.getExtendedTypes().getSupertypes().get(0));
        }
        List<TypeReference> redundantReferences = new ArrayList<TypeReference>();
        List<ClassType> types = new ArrayList<ClassType>();
        int i;
        for (i = 0; i < aSTList.size(); i++) {
            TypeReference tr = aSTList.get(i);
            types.add((ClassType) si.getType(tr));
        }
        for (i = aSTList.size() - 1; i >= 0; i--) {
            TypeReference tr = aSTList.get(i);
            ClassType ct = types.get(i);
            if (superclass != null &&
                    si.isSubtype(superclass, ct)) {
                redundantReferences.add(tr);
            } else {
                for (int j = aSTList.size() - 1; j >= 0; j--) {
                    if (i != j) {
                        ClassType st = types.get(j);
                        if (si.isSubtype(st, ct)) {
                            redundantReferences.add(tr);
                            break;
                        }
                    }
                }
            }
        }
        return redundantReferences;
    }

    public static List<TypeReference> getRedundantExceptions(SourceInfo si, Throws t) {
        ASTList<TypeReference> aSTList = t.getExceptions();
        List<TypeReference> redundantReferences = new ArrayList<TypeReference>();
        List<ClassType> types = new ArrayList<ClassType>(aSTList.size());
        int i;
        for (i = 0; i < aSTList.size(); i++)
            types.add((ClassType) si.getType(aSTList.get(i)));
        for (i = aSTList.size() - 1; i >= 0; i--) {
            ClassType ct = types.get(i);
            for (int j = aSTList.size() - 1; j >= 0; j--) {
                if (i != j) {
                    ClassType st = types.get(j);
                    if (si.isSubtype(ct, st)) {
                        redundantReferences.add(aSTList.get(i));
                        break;
                    }
                }
            }
        }
        return redundantReferences;
    }
}
