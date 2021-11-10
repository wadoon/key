// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.translation;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.ast.declaration.*;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.*;

public class KeYProgModelInfo {
    private TransformationPipelineServices sc = null;
    private final TypeConverter typeConverter;
    private final HashMap<KeYJavaType, HashMap<String, IProgramMethod>> implicits = new LinkedHashMap<>();
    private KeYRecoderExcHandler exceptionHandler = null;

    public KeYProgModelInfo(TypeConverter typeConverter, KeYRecoderExcHandler keh) {
        this(typeConverter);
        exceptionHandler = keh;
    }

    KeYProgModelInfo(TypeConverter typeConverter) {
        this.typeConverter = typeConverter;
    }

    public KeYRecoderExcHandler getExceptionHandler() {
        return exceptionHandler;
    }

    /**
     * Returns all KeY-elements mapped by Recoder2KeY object of this
     * KeYProgModelInfo.
     *
     * @return a Set object containing the KeY-elements.
     */
    public Set<?> allElements() {
        return rec2key().elemsKeY();
    }

    private Collection<MethodUsage> getAllRecoderMethods(KeYJavaType kjt) {
        if (kjt.getJavaType() instanceof TypeDeclaration) {
            var o = (com.github.javaparser.ast.body.TypeDeclaration<?>) rec2key().toRecoder(kjt);
            return o.resolve().getAllMethods();
        }
        return Collections.emptyList();
    }


    /**
     * Returns all visible methods that are defined in this
     * class type or any of its supertypes. The methods are
     * in topological order with respect to the inheritance hierarchy.
     *
     * @return the list of visible methods of this type and its supertypes.
     */
    public ImmutableList<Method> getAllMethods(KeYJavaType kjt) {
        var rmethods = getAllRecoderMethods(kjt);
        ImmutableList<Method> result = ImmutableSLList.nil();
        for (MethodUsage rm : rmethods) {
            Method m = ((IProgramMethod) rec2key().toKeY(rm)).getMethodDeclaration();
            result = result.prepend(m);
        }
        return result;
    }


    /**
     * Returns all visible methods that are defined in this
     * class type or any of its supertypes. The methods are
     * in topological order with respect to the inheritance hierarchy.
     *
     * @return the list of visible methods of this type and its supertypes.
     */

    public ImmutableList<IProgramMethod> getAllProgramMethods(KeYJavaType kjt) {
        var rmethods = getAllRecoderMethods(kjt);
        ImmutableList<IProgramMethod> result = ImmutableSLList.nil();
        for (MethodUsage rm : rmethods) {
            IProgramMethod m = (IProgramMethod) rec2key().toKeY(rm);
            if (m != null) {
                result = result.prepend(m);
            }
        }
        return result;
    }

    private ArrayList<com.github.javaparser.ast.type.Type> getRecoderTypes(ImmutableList<? extends Type> types) {
        if (types == null) {
            return null;
        }

        final var tl = new ArrayList<com.github.javaparser.ast.type.Type>(types.size());
        for (final Type n : types) {
            tl.add(rec2key().toRecoder(n));
        }
        return tl;
    }


    //@SuppressWarnings("unchecked")
    public KeYJavaType resolveType(String shortName, KeYJavaType context) {
        var rt = (com.github.javaparser.ast.body.TypeDeclaration<?>) rec2key().toRecoder(context);
        if (rt instanceof ClassOrInterfaceDeclaration) {
            // check for inner types
            var result = searchType(shortName, ((ClassOrInterfaceDeclaration) rt).getTypes());

            if (result != null) {
                return (KeYJavaType) rec2key().toKeY(result);
            }

            // check for imported types
            var cunit = rt.findCompilationUnit().get();

            for (var i : cunit.getImports()) {
                final List<? extends ClassOrInterfaceDeclaration> types;
                if (i.getPackageReference() != null) {
                    types = sc.getCrossReferenceSourceInfo().getPackage(i.getPackageReference()).getTypes();
                } else {
                    if (i.isMultiImport()) {
                        ClassOrInterfaceDeclaration type = (ClassOrInterfaceDeclaration) sc.getCrossReferenceSourceInfo().getType(i.getTypeReference());
                        types = type.getTypes();
                    } else {
                        types = new LinkedList<>();
                        ((LinkedList<ClassOrInterfaceDeclaration>) types).add((ClassOrInterfaceDeclaration) sc.getCrossReferenceSourceInfo().getType(i.getTypeReference()));
                    }
                }
                result = searchType(shortName, types);
                if (result != null) {
                    return (KeYJavaType) rec2key().toKeY(result);
                }

            }
        }
        return null;

    }

    private ClassOrInterfaceDeclaration searchType(String shortName, final List<? extends ClassType> types) {
        for (var type : types) {
            if (type.getName().equals(shortName)) {
                return type;
            }
        }
        return null;
    }

    /**
     * Returns the full name of a KeYJavaType t.
     *
     * @return the full name of t as a String.
     */

    public String getFullName(KeYJavaType t) {
        var rt = (com.github.javaparser.ast.type.Type) rec2key().toRecoder(t);
        return rt.asClassOrInterfaceType().resolve().getQualifiedName();
    }

    public com.github.javaparser.ast.type.Type getType(TypeReference tr) {
        com.github.javaparser.ast.type.Type result;
        if (tr instanceof TypeRef) {
            result = (com.github.javaparser.ast.type.Type)
                    rec2key().toRecoder(tr.getKeYJavaType());
            return result;
        }
        result = getType(rec2key().toRecoder(tr));
        return result;
    }


    public boolean isFinal(KeYJavaType kjt) {
        var recoderType = (com.github.javaparser.ast.type.Type) rec2key().toRecoder(kjt);
        if (recoderType.isClassOrInterfaceType()) {
            var ref = recoderType.asClassOrInterfaceType().resolve();
            var td = (com.github.javaparser.ast.body.TypeDeclaration) ref.getTypeDeclaration().get().asClass().toAst().get();
            return td.hasModifier(Modifier.Keyword.FINAL);
        } else // array or primitive type
            return false;
    }


    /**
     * Checks whether subType is a subtype of superType or not.
     *
     * @returns true if subType is subtype of superType,
     * false in the other case.
     */

    public boolean isSubtype(KeYJavaType subType, KeYJavaType superType) {
        return isSubtype((com.github.javaparser.ast.type.Type) rec2key().toRecoder(subType),
                (com.github.javaparser.ast.type.Type) rec2key().toRecoder(superType));
    }

    private boolean isSubtype(com.github.javaparser.ast.type.Type subType,
                              com.github.javaparser.ast.type.Type superType) {
        if (subType.isClassOrInterfaceType() && superType.isClassOrInterfaceType()) {
            return isSubtype(subType.asClassOrInterfaceType(),
                    superType.asClassOrInterfaceType());
        } else if (superType.isArrayType() &&
                subType.isArrayType()) {
            return isAssignmentCompatible(subType.asArrayType(), superType.asArrayType());
        } else if (subType instanceof com.github.javaparser.ast.type.ArrayType &&
                superType instanceof ClassOrInterfaceDeclaration) {
            return "java.lang.Object".equals(superType.getFullName())
                    || "Object".equals(superType.getName());
        }
        // should not occur
        throw new RuntimeException("Method isSubtype in class KeYProgModelInfo " +
                "currently only supports two class types or two " +
                "array type but no mixture!");
    }

    private boolean isSubtype(ClassOrInterfaceDeclaration classSubType,
                              ClassOrInterfaceDeclaration classType) {
        boolean isSub = getServConf().getSourceInfo().
                isSubtype(classSubType, classType);
        if (!isSub) {
            boolean result = getServConf().getByteCodeInfo().
                    isSubtype(classSubType, classType);
            return result;
        } else {
            return true;
        }
    }

    /**
     * checks if name refers to a package
     *
     * @param name a String with the name to be checked
     * @return true iff name refers to a package
     */
    public boolean isPackage(String name) {
        return ((recoder.service.DefaultNameInfo) sc.getNameInfo()).isPackage(name);
    }

    /**
     * checks whether subType is assignment compatible to type according
     * to the rules defined in the java language specification
     */
    private boolean isAssignmentCompatible(com.github.javaparser.ast.type.ArrayType subType,
                                           com.github.javaparser.ast.type.ArrayType type) {
        com.github.javaparser.ast.type.Type bt1 = subType.getBaseType();
        com.github.javaparser.ast.type.Type bt2 = type.getBaseType();
        if (bt1 instanceof recoder.abstraction.PrimitiveType &&
                bt2 instanceof recoder.abstraction.PrimitiveType) {
            return bt1.getFullName().equals(bt2.getFullName());
        }
        if (bt1 instanceof ClassOrInterfaceDeclaration &&
                bt2 instanceof ClassOrInterfaceDeclaration)
            return isSubtype((ClassOrInterfaceDeclaration) bt1,
                    (ClassOrInterfaceDeclaration) bt2);
        if (bt1 instanceof com.github.javaparser.ast.type.ArrayType &&
                bt2 instanceof com.github.javaparser.ast.type.ArrayType)
            return isAssignmentCompatible((com.github.javaparser.ast.type.ArrayType) bt1,
                    (com.github.javaparser.ast.type.ArrayType) bt2);
        if (bt1 instanceof ClassOrInterfaceDeclaration &&
                bt2 instanceof com.github.javaparser.ast.type.ArrayType)
            return false;
        if (bt1 instanceof com.github.javaparser.ast.type.ArrayType &&
                bt2 instanceof ClassOrInterfaceDeclaration) {
            if (((ClassOrInterfaceDeclaration) bt2).isInterface()) {
                return bt2.
                        getFullName().equals("java.lang.Cloneable") ||
                        bt2.
                                getFullName().equals("java.lang.Serializable")
                        ;
            } else {
                return bt2.
                        getFullName().equals("java.lang.Object");
            }
        }
        return false;
    }

    private List<com.github.javaparser.ast.body.MethodDeclaration> getRecoderMethods(KeYJavaType kjt) {
        if (kjt.getJavaType() instanceof TypeDeclaration) {
            Object o = rec2key().toRecoder(kjt);
            if (o instanceof ClassOrInterfaceDeclaration) {
                ClassOrInterfaceDeclaration rct
                        = (ClassOrInterfaceDeclaration) o;
                return rct.getProgramModelInfo().getMethods(rct);
            }
        }
        return new ArrayList<>();
    }

    private List<? extends com.github.javaparser.ast.body.ConstructorDeclaration > getRecoderConstructors(KeYJavaType ct) {
        
        ClassOrInterfaceDeclaration rct
                = (ClassOrInterfaceDeclaration) rec2key().toRecoder(ct);
        return rct.getProgramModelInfo().getConstructors(rct);
    }

    private List<com.github.javaparser.ast.body.MethodDeclaration> getRecoderMethods(
            KeYJavaType ct, String m, ImmutableList<? extends Type> signature, KeYJavaType context) {
        var rct = (ClassOrInterfaceDeclaration) rec2key().toRecoder(ct);
        var rcontext = rec2key().toRecoder(context);

        return rct.getProgramModelInfo().getMethods(rct, m,
                getRecoderTypes(signature),
                null,  // no generic type variables yet
                rcontext);
    }


    private List<com.github.javaparser.ast.body.ConstructorDeclaration>
    getRecoderConstructors(KeYJavaType ct, ImmutableList<KeYJavaType> signature) {
        var rct = (ClassOrInterfaceDeclaration) rec2key().toRecoder(ct);
        return rct.getConstructors();
        /*List<? extends com.github.javaparser.ast.body.ConstructorDeclaration > res
                = rct.getProgramModelInfo().getConstructors
                (rct, getRecoderTypes(signature));
        return res;*/
    }


    /**
     * Returns the list of most specific methods with the given
     * name that are defined in the given type or in a supertype
     * where they are visible for the given type, and have a signature
     * that is compatible to the given one. If used to resolve a
     * method call, the result should be defined and unambiguous.
     *
     * @param ct        the class type to get methods from.
     * @param m         the name of the methods in question.
     * @param signature the statical type signature of a callee.
     */

    public ImmutableList<Method> getMethods(KeYJavaType ct, String m,
                                            ImmutableList<Type> signature, KeYJavaType context) {
        var rml = getRecoderMethods(ct, m, signature, context);
        ImmutableList<Method> result = ImmutableSLList.nil();
        for (com.github.javaparser.ast.body.MethodDeclaration rm : rml) {
            Method method = (Method) rec2key().toKeY(rm);
            result = result.prepend(method);
        }
        return result;
    }


    /**
     * Returns the methods locally defined within the given
     * class type. If the type is represented in source code,
     * the returned list matches the syntactic order.
     *
     * @param ct a class type.
     */
    public ImmutableList<Method> getMethods(KeYJavaType ct) {
        var rml = getRecoderMethods(ct);
        ImmutableList<Method> result = ImmutableSLList.nil();
        for (var rm : rml) {
            if (!(rm instanceof recoder.bytecode.MethodInfo)) {
                Method m = ((IProgramMethod) rec2key().toKeY(rm)).getMethodDeclaration();
                result = result.prepend(m);
            }
        }
        return result;
    }

    /**
     * Returns the ProgramMethods locally defined within the given
     * class type. If the type is represented in source code,
     * the returned list matches the syntactic order.
     *
     * @param ct a class type.
     */
    public ImmutableList<ProgramMethod> getAllProgramMethodsLocallyDeclared(KeYJavaType ct) {
        List<com.github.javaparser.ast.body.MethodDeclaration> rml = getRecoderMethods(ct);
        ImmutableList<ProgramMethod> result = ImmutableSLList.nil();
        for (int i = rml.size() - 1; i >= 0; i--) {
            com.github.javaparser.ast.body.MethodDeclaration rm = rml.get(i);
            if (!(rm instanceof recoder.bytecode.MethodInfo)) {
                result = result.prepend((ProgramMethod) rec2key().toKeY(rm));
            }
        }
        return result;
    }

    /**
     * Returns the constructors locally defined within the given
     * class type. If the type is represented in source code,
     * the returned list matches the syntactic order.
     *
     * @param ct a class type.
     */

    public ImmutableList<IProgramMethod> getConstructors(KeYJavaType ct) {
        List<? extends Constructor> rcl = getRecoderConstructors(ct);
        ImmutableList<IProgramMethod> result = ImmutableSLList.nil();
        for (int i = rcl.size() - 1; i >= 0; i--) {
            com.github.javaparser.ast.body.MethodDeclaration rm = rcl.get(i);
            IProgramMethod m = (IProgramMethod) rec2key().toKeY(rm);
            if (m != null) {
                result = result.prepend(m);
            }
        }
        return result;
    }

    /**
     * retrieves the most specific constructor declared in the given type with
     * respect to the given signature
     *
     * @param ct        the KeYJavyType where to look for the constructor
     * @param signature IList<KeYJavaType> representing the signature of the constructor
     * @return the most specific constructor declared in the given type
     */
    public IProgramMethod getConstructor(KeYJavaType ct,
                                         ImmutableList<KeYJavaType> signature) {
        List<? extends com.github.javaparser.ast.body.ConstructorDeclaration > constructors =
                getRecoderConstructors(ct, signature);
        if (constructors.size() == 1) {
            return (IProgramMethod) rec2key().toKeY(constructors.get(0));
        }
        if (constructors.size() == 0) {
            Debug.out("javainfo: Constructor not found: ", ct);
            return null;
        }
        Debug.fail();
        return null;
    }

    /**
     * retrieves implicit methods
     */
    private IProgramMethod getImplicitMethod(KeYJavaType ct, String name) {
        final HashMap<String, IProgramMethod> m = implicits.get(ct);
        if (m != null) {
            final IProgramMethod pm = m.get(name);
            if (pm != null) {
                return pm;
            }
        }
        TypeDeclaration cd = (TypeDeclaration) ct.getJavaType();
        ImmutableArray<MemberDeclaration> members = cd.getMembers();
        for (int i = 0; i < members.size(); i++) {
            final MemberDeclaration member = members.get(i);
            if (member instanceof IProgramMethod &&
                    ((IProgramMethod) member).getMethodDeclaration().getName().equals(name)) {
                return (IProgramMethod) member;
            }
        }
        Debug.out("keyprogmodelinfo: implicit method %1 not found in %2 (%1, %2) ",
                name, ct);
        return null;
    }


    /**
     * Returns the IProgramMethods with the given name that is defined
     * in the given type or in a supertype where it is visible for the
     * given type, and has a signature that is compatible to the given one.
     *
     * @param ct        the class type to get methods from.
     * @param m         the name of the methods in question.
     * @param signature the statical type signature of a callee.
     * @return the IProgramMethods, if one is found,
     * null if none or more than one IProgramMethod is found (in this case
     * a debug output is written to console).
     */
    public IProgramMethod getProgramMethod(KeYJavaType ct, String m,
                                           ImmutableList<? extends Type> signature,
                                           KeYJavaType context) {
        if (ct.getJavaType() instanceof ArrayType ||
                context.getJavaType() instanceof ArrayType) {
            return getImplicitMethod(ct, m);
        }

        List<com.github.javaparser.ast.body.MethodDeclaration> methodlist =
                getRecoderMethods(ct, m, signature, context);

        if (methodlist.size() == 1) {
            return (IProgramMethod) rec2key().toKeY(methodlist.get(0));
        } else if (methodlist.size() == 0) {
            Debug.out("javainfo: Program Method not found: ", m);
            return null;
        } else {
            Debug.fail();
            return null;
        }
    }


    /**
     * returns the same fields as given in <tt>rfl</tt> and returns
     * their KeY representation
     *
     * @param rfl the List of fields to be looked up
     * @return list with the corresponding fields as KeY datastructures
     */
    private ImmutableList<Field> asKeYFields(List<? extends com.github.javaparser.ast.body.FieldDeclaration> rfl) {
        ImmutableList<Field> result = ImmutableSLList.nil();
        if (rfl == null) {
            // this occurs for the artificial Null object at the moment
            // should it have implicit fields?
            return result;
        }
        for (int i = rfl.size() - 1; i >= 0; i--) {
            com.github.javaparser.ast.body.FieldDeclaration rf = rfl.get(i);
            Field f = (Field) rec2key().toKeY(rf);
            if (f != null) {
                result = result.prepend(f);
            } else {
                Debug.out("Field has no KeY equivalent (recoder field):", rf.getFullName());
                Debug.out("This happens currently as classes only available in byte code " +
                        "are only partially converted ");
            }
        }
        return result;
    }

    /**
     * returns the fields defined within the given class type.
     * If the type is represented in source code, the returned list
     * matches the syntactic order.
     *
     * @param ct the class type whose fields are returned
     * @return the list of field members of the given type.
     */
    public ImmutableList<Field> getAllFieldsLocallyDeclaredIn(KeYJavaType ct) {
        if (ct.getJavaType() instanceof ArrayType) {
            return getVisibleArrayFields(ct);
        }
        ClassOrInterfaceDeclaration rct = (ClassOrInterfaceDeclaration) rec2key().toRecoder(ct);

        return asKeYFields(rct.getProgramModelInfo().getFields(rct));
    }


    /**
     * returns all in <tt>ct</tt> visible fields
     * declared in <tt>ct</tt> or one of its supertypes
     * in topological order starting with the fields of
     * the given type
     * If the type is represented in source code, the returned list
     * matches the syntactic order.
     *
     * @param ct the class type whose fields are returned
     * @return the list of field members of the given type.
     */
    public ImmutableList<Field> getAllVisibleFields(KeYJavaType ct) {
        if (ct.getJavaType() instanceof ArrayDeclaration) {
            return getVisibleArrayFields(ct);
        }

        ClassOrInterfaceDeclaration rct
                = (ClassOrInterfaceDeclaration) rec2key().toRecoder(ct);
        List<com.github.javaparser.ast.body.FieldDeclaration> rfl =
                rct.getProgramModelInfo().getAllFields(rct);

        return asKeYFields(rfl);
    }

    /**
     * returns all fields of and visible in an array field
     *
     * @param arrayType the KeYJavaType of the array
     * @return the list of visible fields
     */
    private ImmutableList<Field> getVisibleArrayFields(KeYJavaType arrayType) {
        ImmutableList<Field> result = ImmutableSLList.nil();

        final ImmutableArray<MemberDeclaration> members =
                ((ArrayDeclaration) arrayType.getJavaType()).getMembers();

        for (int i = members.size() - 1; i >= 0; i--) {
            final MemberDeclaration member = members.get(i);
            if (member instanceof FieldDeclaration) {
                final ImmutableArray<FieldSpecification> specs =
                        ((FieldDeclaration) member).getFieldSpecifications();
                for (int j = specs.size() - 1; j >= 0; j--) {
                    result = result.prepend(specs.get(j));
                }
            }
        }

        //      fields of java.lang.Object visible in an array
        final ImmutableList<Field> javaLangObjectField =
                getAllVisibleFields((KeYJavaType) rec2key().
                        toKeY(sc.getNameInfo().getJavaLangObject()));

        for (Field aJavaLangObjectField : javaLangObjectField) {
            final Field f = aJavaLangObjectField;

            if (!((com.github.javaparser.ast.body.FieldDeclaration)
                    rec2key().toRecoder(f)).isPrivate()) {
                result = result.append(f);
            }
        }
        return result;
    }

    /**
     * returns all proper subtypes of class <code>ct</code> (i.e. without <code>ct</code> itself)
     */
    private List<ClassOrInterfaceDeclaration> getAllRecoderSubtypes(KeYJavaType ct) {
        return sc.getCrossReferenceSourceInfo().
                getAllSubtypes((ClassOrInterfaceDeclaration) rec2key().toRecoder(ct));
    }

    /**
     * returns all supertypes of the given class type with the type itself as
     * first element
     */
    private List<ClassOrInterfaceDeclaration> getAllRecoderSupertypes(KeYJavaType ct) {
        return sc.getCrossReferenceSourceInfo().
                getAllSupertypes((ClassOrInterfaceDeclaration) rec2key().toRecoder(ct));
    }


    /**
     * returns a list of KeYJavaTypes representing the given recoder types in
     * the same order
     *
     * @param rctl the ASTList<ClassType> to be converted
     * @return list of KeYJavaTypes representing the given recoder types in
     * the same order
     */
    private ImmutableList<KeYJavaType> asKeYJavaTypes(final List<ClassOrInterfaceDeclaration> rctl) {
        ImmutableList<KeYJavaType> result = ImmutableSLList.nil();
        for (int i = rctl.size() - 1; i >= 0; i--) {
            final ClassOrInterfaceDeclaration rct = rctl.get(i);
            final KeYJavaType kct = (KeYJavaType) rec2key().toKeY(rct);
            if (kct != null) {
                result = result.prepend(kct);
            }
        }
        return result;
    }

    /**
     * Returns all known supertypes of the given class type with the type itself
     * as first element.
     *
     * @param ct a class type
     * @return the list of the known subtypes of the given class type.
     */
    public ImmutableList<KeYJavaType> getAllSupertypes(KeYJavaType ct) {
        return asKeYJavaTypes(getAllRecoderSupertypes(ct));
    }

    /**
     * Returns all proper subtypes of the given class type
     *
     * @param ct a class type
     * @return the list of the known subtypes of the given class type.
     */
    public ImmutableList<KeYJavaType> getAllSubtypes(KeYJavaType ct) {
        return asKeYJavaTypes(getAllRecoderSubtypes(ct));
    }

    private Recoder2KeY createRecoder2KeY(NamespaceSet nss) {
        return new Recoder2KeY(services, sc, rec2key(), nss, typeConverter, cp);
    }

    /**
     * Parses a given JavaBlock using cd as context to determine the right
     * references.
     *
     * @param block a String describing a java block
     * @param cd    ClassDeclaration representing the context in which the
     *              block has to be interpreted.
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlock(String block, ClassDeclaration cd,
                               NamespaceSet nss) {
        return createRecoder2KeY(nss).readBlock(block, new Context
                (sc, (recoder.java.declaration.ClassDeclaration)
                        rec2key().toRecoder(cd)));
    }


    /**
     * Parses a given JavaBlock using an empty context.
     *
     * @param block a String describing a java block
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readJavaBlock(String block, NamespaceSet nss) {
        return createRecoder2KeY(nss).readBlockWithEmptyContext(block);
    }


    public ImmutableList<KeYJavaType> findImplementations
            (Type ct, String name, ImmutableList<KeYJavaType> signature) {

        // set up recoder inputs
        ClassOrInterfaceDeclaration rct =
                (ClassOrInterfaceDeclaration) rec2key().toRecoder(ct);
        // transform the signature up to recoder conventions
        ArrayList<com.github.javaparser.ast.type.Type> rsignature =
                new ArrayList<>(signature.size());
        Iterator<KeYJavaType> i = signature.iterator();
        int j = 0;
        while (i.hasNext()) {
            rsignature.add(j, (com.github.javaparser.ast.type.Type)
                    rec2key().toRecoder(i.next()));
            j++;
        }

        // If ct is an interface, but does not declare the method, we
        // need to start the search "upstairs"

        while (rct.isInterface() && !isDeclaringInterface(rct, name, rsignature)) {
            rct = rct.getAllSupertypes().get(1);
        }


        ImmutableList<KeYJavaType> classList = ImmutableSLList.nil();
        classList = recFindImplementations(rct, name, rsignature, classList);


        if (!declaresApplicableMethods(rct, name, rsignature)) {
            // ct has no implementation, go up
            List<ClassOrInterfaceDeclaration> superTypes = rct.getAllSupertypes();
            int k = 0;
            while (k < superTypes.size() &&
                    !declaresApplicableMethods(superTypes.get(k),
                            name, rsignature)) k++;
            if (k < superTypes.size()) {
                rct = superTypes.get(k);
                KeYJavaType r = (KeYJavaType) mapping.toKeY(rct);
                if (r == null) {
                    System.out.println("Type " + rct.getName());
                } else {
                    classList = classList.append(r);
                }
            } // no implementation is needed if classes above are abstract
        }

        return classList;
    }


    private ImmutableList<KeYJavaType> recFindImplementations(
            ClassOrInterfaceDeclaration ct,
            String name,
            List<com.github.javaparser.ast.type.Type> signature,
            ImmutableList<KeYJavaType> result) {
        recoder.service.CrossReferenceSourceInfo si
                = getServConf().getCrossReferenceSourceInfo();

        if (declaresApplicableMethods(ct, name, signature)) {
            KeYJavaType r = (KeYJavaType) mapping.toKeY(ct);
            if (r == null) {
                System.out.println("Type " + ct.getFullName() + ":" + name + " not found");
            } else if (!result.contains(r)) {
                result = result.prepend(r);
            }
        }

        List<ClassOrInterfaceDeclaration> classes = si.getSubtypes(ct);

        //alpha sorting to make order deterministic
        ClassOrInterfaceDeclaration[] classesArray =
                classes.toArray(new ClassOrInterfaceDeclaration[classes.size()]);
        java.util.Arrays.sort(classesArray, new java.util.Comparator<>() {
            public int compare(ClassOrInterfaceDeclaration o1, ClassOrInterfaceDeclaration o2) {
                return o2.getFullName().compareTo(o1.getFullName());
            }
        });

        for (ClassOrInterfaceDeclaration c : classesArray) {
            result = recFindImplementations(c, name, signature, result);
        }
        return result;
    }


    private boolean declaresApplicableMethods(ClassOrInterfaceDeclaration ct,
                                              String name,
                                              List<com.github.javaparser.ast.type.Type> signature) {
        recoder.service.CrossReferenceSourceInfo si
                = getServConf().getCrossReferenceSourceInfo();

        List<com.github.javaparser.ast.body.MethodDeclaration> list = si.getMethods(ct);
        int s = list.size();
        int i = 0;
        while (i < s) {
            com.github.javaparser.ast.body.MethodDeclaration m = list.get(i);
            if (name.equals(m.getName())
                    && si.isCompatibleSignature(signature, m.getSignature())
                    && si.isVisibleFor(m, ct)
                    && !m.isAbstract()) return true;
            else i++;
        }
        return false;
    }

    private boolean isDeclaringInterface(ClassOrInterfaceDeclaration ct,
                                         String name,
                                         List<com.github.javaparser.ast.type.Type> signature) {
        Debug.assertTrue(ct.isInterface());

        List<com.github.javaparser.ast.body.MethodDeclaration> list = ct.getMethods();
        int s = list.size();
        int i = 0;
        while (i < s) {
            com.github.javaparser.ast.body.MethodDeclaration m = list.get(i);
            if (name.equals(m.getName())
                    && si.isCompatibleSignature(signature, m.getSignature())
                    && si.isVisibleFor(m, ct)) return true;
            else i++;
        }
        return false;
    }

    public void putImplicitMethod(IProgramMethod m, KeYJavaType t) {
        HashMap<String, IProgramMethod> map = implicits.get(t);
        if (map == null) {
            map = new LinkedHashMap<>();
            implicits.put(t, map);
        }
        map.put(m.name().toString(), m);
    }


    public KeYProgModelInfo copy() {
        return new KeYProgModelInfo(typeConverter.copy(null), exceptionHandler);
    }

    public Recoder2KeY rec2key() {
        return null;
    }
}