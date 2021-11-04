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

package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.ThrowStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import de.uka.ilkd.key.util.Debug;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Transforms the constructors of the given class to their
 * normalform. The constructor normalform can then be accessed via a
 * methodcall <code>&lt;init&gt;<cons_args)</code>. The visibility of
 * the normalform is the same as for the original constructor.
 */
public class ConstructorNormalformBuilder extends JavaTransformer {

    public static final String CONSTRUCTOR_NORMALFORM_IDENTIFIER = "<init>";

    public static final String OBJECT_INITIALIZER_IDENTIFIER = "<objectInitializer>";

    private final HashMap<TypeDeclaration<?>, List<ConstructorDeclaration>> class2constructors;
    private final HashMap<TypeDeclaration<?>, FieldDeclaration> class2enclosingThis;
    private final HashMap<TypeDeclaration<?>, TypeDeclaration<?>> class2enclosingClass;
    private final HashMap<TypeDeclaration<?>, NodeList<Statement>> class2initializers;
    private final HashMap<TypeDeclaration<?>, NameExpr> class2identifier;
    private final HashMap<TypeDeclaration<?>, NodeList<MethodDeclaration>> class2methodDeclaration;
    private final HashMap<TypeDeclaration<?>, ClassOrInterfaceType> class2superContainer;
    private final HashMap<NameExpr, Type> v2t;
//    private HashMap class2fieldsForFinalVars;

    private ClassOrInterfaceType javaLangObject;

    /**
     * creates the constructor normalform builder
     */
    public ConstructorNormalformBuilder(TransformationPipelineServices services) {
        super(services);
        List<CompilationUnit> units = cache.getUnits();
        class2constructors = new LinkedHashMap<>(4 * units.size());
        class2initializers = new LinkedHashMap<>(10 * units.size());
        class2methodDeclaration = new LinkedHashMap<>(10 * units.size());
        class2enclosingThis = new LinkedHashMap<>(units.size());
        class2enclosingClass = new LinkedHashMap<>(units.size());
        class2identifier = new LinkedHashMap<>(units.size());
        class2superContainer = new LinkedHashMap<>(units.size());
        v2t = new LinkedHashMap<>(units.size());
//	class2fieldsForFinalVars = new HashMap(units.size());
    }


    /**
     * The list of statements is the smallest list that contains a copy
     * assignment for each instance field initializer of class cd,
     * e.g. <code> i = 0; </code> for <code> public int i = 0; </code> or
     * a reference to the private method
     * <code>&lt;objectInitializer&gt;<i>i</i> refering to the i-th object
     * initializer of cd. These private declared methods are created on
     * the fly. Example for
     * <code><pre>
     * class C {
     * int i = 0;
     * {
     * int j = 3;
     * i = j + 5;
     * }
     * <p>
     * public C () {} ...
     * }</pre>
     * </code> the following list of size two is returned
     * <code><pre>
     * [ i = 0;,  &lt;objectInitializer&gt;0(); ]
     * </pre></code>
     * where <code><pre>
     * private &lt;objectInitializer&gt;0() {
     * int j = 3;
     * i = j + 5;
     * }</pre>
     * </code>
     *
     * @param cd the TypeDeclaration<?> of which the initilizers have to
     *           be collected
     * @return the list of copy assignments and method references
     * realising the initializers.
     */
    private NodeList<Statement> collectInitializers(ClassOrInterfaceDeclaration cd) {
        NodeList<Statement> result = new NodeList<>();
        NodeList<MethodDeclaration> mdl = new NodeList<>();

        var initializers =
                cd.getMembers().stream()
                        .filter(BodyDeclaration::isInitializerDeclaration)
                        .map(it -> (InitializerDeclaration) it)
                        .filter(it -> !it.isStatic())
                        .collect(Collectors.toList());


        for (InitializerDeclaration initializer : initializers) {
            NodeList<Modifier> mods = new NodeList<>(
                    new Modifier(Modifier.Keyword.PRIVATE)
            );

            String name = OBJECT_INITIALIZER_IDENTIFIER + mdl.size();
            var initializerMethod = cd.addMethod(name, mods);
            initializerMethod.setBody(initializer.getBody().clone());
            mdl.add(initializerMethod);
            result.add(new ExpressionStmt(new MethodCallExpr(null, new NameExpr(name)));
        }

        var memberFields =
                cd.getMembers().stream()
                        .filter(BodyDeclaration::isFieldDeclaration)
                        .map(it -> (FieldDeclaration) it)
                        .filter(it -> !it.isStatic())
                        .collect(Collectors.toList());

        for (FieldDeclaration field : memberFields) {
            for (VariableDeclarator variable : field.getVariables()) {
                if ((variable.getInitializer().isPresent()) {
                    Expression fieldInit = variable.getInitializer().get();
                    final var access = new FieldAccessExpr(
                            new ThisExpr(), new NodeList<>(), variable.getName());
                    var fieldCopy = new AssignExpr(access, fieldInit.clone(), AssignExpr.Operator.ASSIGN);
                    result.add(new ExpressionStmt(fieldCopy));
                }
            }
        }
        return result;
    }

    /**
     * Two-pass transformation have to be strictly divided up into two
     * parts. the first part analyzes the model and collects all
     * necessary information. In this case all class declarations are
     * examined and initializers as well as constructors are collected.
     * All actions, which may cause a recoder model update have to be
     * done here.
     *
     * @return status report if analyze encountered problems or not
     */
    public void analyze() {
        javaLangObject = services.getNameInfo().getJavaLangObject();
        if (!(javaLangObject instanceof TypeDeclaration<?>)) {
            Debug.fail("Could not find class java.lang.Object or only as bytecode");
        }
        for (final TypeDeclaration<?> cd : TypeDeclaration < ?>s()){
            if (cd.getName() == null || cd.getStatementContainer() != null) {
                (new FinalOuterVarsCollector()).walk(cd);
            }
            // collect constructors for transformation phase
            var constructors = new ArrayList<ConstructorDeclaration>();
            constructors.addAll(services.getSourceInfo().getConstructors(cd));
            if (constructors.size() == 0 && (cd.getContainingReferenceType() != null && !cd.isStatic() ||
                    cd.getName() == null || cd.getStatementContainer() != null)) {
                constructors.add(new DefaultConstructor(cd));
            }
            class2constructors.put(cd, constructors);

            class2identifier.put(cd, getId(cd));

            class2enclosingThis.put(cd, getImplicitEnclosingThis(cd));

            if (cd.getAllSupertypes().size() > 1 && (cd.getStatementContainer() != null || cd.getName() == null)) {
                class2superContainer.put(cd, cd.getAllSupertypes().get(1).getContainingReferenceType());
            }

            final List<Variable> finalVars = getLocalClass2FinalVar().get(cd);
            if (finalVars != null) {
                for (final Variable v : finalVars) {
                    v2t.put(v, v.getType());
                }
            }

            if (cd.getName() == null ||
                    cd.getStatementContainer() != null ||
                    cd.getContainingReferenceType() != null && !cd.isStatic()) {
                class2enclosingClass.put(cd, containingClass(cd));
            }

            // collect initializers for transformation phase
            class2initializers.put(cd, collectInitializers(cd));
        }
    }

    protected Optional<FieldDeclaration> getImplicitEnclosingThis(TypeDeclaration<?> cd) {
        return cd.getFieldByName(ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS);
    }

    private void attachDefaultConstructor(TypeDeclaration<?> cd) {
        NodeList<Modifier> mods = new NodeList<>(
                new Modifier(Modifier.Keyword.PUBLIC)
        );
        NodeList<Parameter> parameters = new NodeList<>();
        ThrowStmt recThrows;
        BlockStmt body;
        recThrows = null;
        body = new BlockStmt();
        attach(new MethodCallExpr(new SuperExpr(),
                new NameExpr(CONSTRUCTOR_NORMALFORM_IDENTIFIER)), body, 0);
        final Iterator<Statement> initializers = class2initializers.get(cd).iterator();
        for (int i = 0; initializers.hasNext(); i++) {
            attach(initializers.next().clone(), body, i + 1);
        }
        MethodDeclaration def = new MethodDeclaration(mods,
                null, // return type is void
                new NameExpr(CONSTRUCTOR_NORMALFORM_IDENTIFIER),
                parameters,
                recThrows,
                body);
        attach(def, cd, 0);
    }

    /**
     * Creates the normalform of the given constructor, that is declared
     * in class cd. For a detailed description of the normalform to be
     * built see the KeY Manual.
     *
     * @param cd   the TypeDeclaration<?> where the cons is declared
     * @param cons the Constructor to be transformed
     * @return the constructor normalform
     */
    private MethodDeclaration normalform(TypeDeclaration<?> cd, ConstructorDeclaration cons) {
        NodeList<Modifier> mods = new NodeList<>();
        NodeList<Parameter> parameters;
        ThrowStmt recThrows;
        BlockStmt body;
        FieldDeclaration et = class2enclosingThis.get(cd);
        TypeDeclaration td = class2enclosingClass.get(cd);
        var outerVars = getLocalClass2FinalVar().get(cd);
        int j = et == null ? 0 : 1;
        if (outerVars != null) j += outerVars.size();
        Parameter pd = null;
        AssignExpr ca = null;
        String etId = "_ENCLOSING_THIS";
        if (et != null) {
            pd = new Parameter(
                    new Type(td.getIdentifier().clone()),
                    new Identifier(etId));
            ca = new AssignExpr(new FieldReference(new ThisReference(), new NameExpr(et.getName())),
                    new VariableReference(new Identifier(etId)));
        }

        if (!(cons instanceof ConstructorDeclaration)) {
            mods.add(new Public());
            parameters = new NodeList<Parameter>(0 + j);
            recThrows = null;
            body = new BlockStmt();
        } else {
            ConstructorDeclaration consDecl = (ConstructorDeclaration) cons;
            mods = (consDecl.getModifiers() == null ? null : consDecl.getModifiers().clone());
            parameters = consDecl.getParameters().clone();
            recThrows = consDecl.getThrown() == null ? null : consDecl.getThrown().clone();

            BlockStmt origBody = consDecl.getBody();
            if (origBody == null) // may happen if a stub is defined with an empty constructor
                body = null;
            else
                body = origBody.clone();
        }

        if (outerVars != null && !outerVars.isEmpty()) {
            if (parameters.isEmpty()) {
                attachDefaultConstructor(cd);
            }

            for (final Variable v : outerVars) {
                parameters.add(new Parameter(
                        new Type(new Identifier(v2t.get(v).getName())),
                        new Identifier(v.getName())));
            }
        }

        if (pd != null) {
            if (parameters.isEmpty()) {
                attachDefaultConstructor(cd);
            }
            parameters.add(pd);
        }

        if (cd != javaLangObject && body != null) {
            // remember original first statement
            Statement first = body.getStatementCount() > 0 ?
                    body.getStatementAt(0) : null;

            // first statement has to be a this or super constructor call
            if (!(first instanceof SpecialConstructorReference)) {
                if (body.getBody() == null) {
                    body.setBody(new NodeList<Statement>());
                }
                attach(new MethodCallExpr
                        (new SuperExpr(), new NameExpr
                                (CONSTRUCTOR_NORMALFORM_IDENTIFIER)), body, 0);
            } else {
                body.getBody().remove(0);
                if (first instanceof ThisConstructorReference) {
                    attach(new MethodCallExpr
                            (new ThisReference(), new NameExpr
                                    (CONSTRUCTOR_NORMALFORM_IDENTIFIER),
                                    ((SpecialConstructorReference) first).getArguments()), body, 0);
                } else {
                    ReferencePrefix referencePrefix = ((SuperConstructorReference) first).getReferencePrefix();
                    NodeList<Expression> args = ((SpecialConstructorReference) first).getArguments();
                    if (referencePrefix != null && referencePrefix instanceof Expression) {
                        if (args == null) args = new NodeList<Expression>(1);
                        args.add((Expression) referencePrefix);
                    } else if (class2superContainer.get(cd) != null) {
                        if (args == null) args = new NodeList<Expression>(1);
                        args.add(new VariableReference(new Identifier(etId)));
                    }
                    attach(new MethodCallExpr
                                    (new SuperExpr(), new NameExpr
                                            (CONSTRUCTOR_NORMALFORM_IDENTIFIER),
                                            args),
                            body, 0);
                }
            }
            // if the first statement is not a this constructor reference
            // the instance initializers have to be added in source code
            // order
            if (!(first instanceof ThisConstructorReference)) {
                NodeList<Statement> initializers = class2initializers.get(cd);
                if (ca != null) {
                    attach(ca, body, 0);
                }
                for (int i = 0; outerVars != null && i < outerVars.size(); i++) {
                    attach(new AssignExpr(new FieldReference(new ThisReference(),
                                    new NameExpr(ImplicitFieldAdder.FINAL_VAR_PREFIX +
                                            (outerVars.get(i)).getName())),
                                    new VariableReference(new Identifier(outerVars.get(i).getName()))), body,
                            i + (ca != null ? 1 : 0));
                }
                for (int i = 0; i < initializers.size(); i++) {
                    attach(initializers.get(i).clone(), body, i + 1 + j);
                }

            }
        }


        MethodDeclaration nf = new MethodDeclaration
                (mods,
                        null, // return type is void
                        new NameExpr(CONSTRUCTOR_NORMALFORM_IDENTIFIER),
                        parameters,
                        recThrows,
                        body);
        nf.makeAllParentRolesValid();
        return nf;
    }

    private ConstructorDeclaration attachConstructorDecl(TypeDeclaration td) {
        if (td.getParentNode().get() instanceof New) {
            New n = (New) td.getParentNode().get();
            if (n.getArguments() == null || n.getArguments().size() == 0) return null;
            ConstructorDeclaration constr = services.getCrossReferenceSourceInfo().getConstructorDeclaration(
                    services.getCrossReferenceSourceInfo().getConstructor(n));
            constr = constr.clone();
            SuperConstructorReference sr = new SuperConstructorReference(
                    n.getArguments() != null ? n.getArguments().clone() :
                            new NodeList<Expression>(0));
            constr.setBody(new BlockStmt(new NodeList<Statement>(sr)));
            constr.makeAllParentRolesValid();
            attach(constr, td, 0);
            return constr;
//            recoder.kit.transformation.AppendMember am = 
//                new recoder.kit.transformation.AppendMember(servConf, true, constr, cd);
//            am.analyze();
//            am.transform();
//            System.out.println(((ConstructorDeclaration) servConf.getCrossReferenceSourceInfo().getConstructors(cd).getConstructor(0)).toSource());
        }
        return null;
    }

    /**
     * entry method for the constructor normalform builder
     *
     * @param td the TypeDeclaration
     */
    protected void apply(TypeDeclaration<?> td) {
        if (td instanceof ClassOrInterfaceDeclaration) {
            var cd = (ClassOrInterfaceDeclaration) td;
            var constructors = class2constructors.get(td);
            ConstructorDeclaration anonConstr = null;
            if (cd.getName() == null) {
                anonConstr = attachConstructorDecl(td);
            }
            if (anonConstr != null) constructors.add(anonConstr);
            for (int i = 0; i < constructors.size(); i++) {
                normalform(td, constructors.get(i));
            }

            NodeList<MethodDeclaration> mdl = class2methodDeclaration.get(td);
            for (MethodDeclaration md : mdl) {
                cd.addMember(md);
            }
        }
    }
}