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

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.validator.ProblemReporter;
import de.uka.ilkd.key.util.Debug;

import javax.lang.model.type.ReferenceType;
import java.util.List;


/**
 * The Java DL requires some implicit fields and methods, that are
 * available in each Java class. The name of the implicit fields/methods
 * is usually enclosed between two angle brackets. To access them in a
 * uniform way, they are added as usual fields to the classes, in
 * particular this makes it possible to parse them in a natural way.
 * The ImplicitFieldAdder is responsible to add all implicit fields to
 * the type declarations of the model. As the implicit methods and only
 * them will access these fields, this transformer has to be executed
 * before the other transformers are called.
 */
public class ImplicitFieldAdder extends JavaTransformer {

    public static final String IMPLICIT_CLASS_PREPARED = "<classPrepared>";
    public static final String IMPLICIT_CLASS_INITIALIZED = "<classInitialized>";
    public static final String IMPLICIT_CLASS_INIT_IN_PROGRESS = "<classInitializationInProgress>";
    public static final String IMPLICIT_CLASS_ERRONEOUS = "<classErroneous>";
    public static final String IMPLICIT_CREATED = "<created>";
    public static final String IMPLICIT_INITIALIZED = "<initialized>";
    public static final String IMPLICIT_TRANSIENT = "<transient>";
    public static final String IMPLICIT_TRANSACTION_UPDATED = "<transactionConditionallyUpdated>";
    public static final String IMPLICIT_ENCLOSING_THIS = "<enclosingThis>";
    public static final String FINAL_VAR_PREFIX = "_outer_final_";

    /**
     * flag set if java.lang.Object has been already transformed
     */
    private boolean transformedObject = false;
    private ReferenceType javaLangObject;

    /**
     * creates a transformation that adds all implicit fields,
     * for example <code>&lt;created&gt;</code>,
     * <code>&lt;initialized&gt;</code> and
     * <code>&lt;nextToCreate&gt;</code> etc.
     *
     * @param services the CrossReferenceServiceConfiguration to access
     *                 model information
     * @param cache    a cache object that stores information which is needed by
     *                 and common to many transformations. it includes the compilation units,
     *                 the declared classes, and information for local classes.
     */
    public ImplicitFieldAdder(TransformationPipelineServices services,
                              TransformerCache cache) {
        super(services, cache);
    }

    /**
     * creates an implicit field of the given type and name
     *
     * @param typeName  the name of the type of the new field to create
     * @param fieldName the name of the field
     * @param isStatic  a boolean that is true if the field has to be
     *                  created as static (class) field
     * @return the new created field declaration
     */
    public static FieldDeclaration createImplicitRecoderField(
            String typeName, String fieldName, boolean isStatic, boolean isPrivate) {
        return createImplicitRecoderField(typeName, fieldName, isStatic, isPrivate, false);
    }

    public static FieldDeclaration createImplicitRecoderField(
            String typeName, String fieldName, boolean isStatic, boolean isPrivate, boolean isFinal) {
        NodeList<Modifier> modifiers = new NodeList<>(3);
        if (isStatic) {
            modifiers.add(new Modifier(Modifier.Keyword.STATIC));
        }
        if (isPrivate) {
            modifiers.add(new Modifier(Modifier.Keyword.PRIVATE));
        } else {
            modifiers.add(new Modifier(Modifier.Keyword.PUBLIC));
        }

        if (isFinal) {
            modifiers.add(new Modifier(Modifier.Keyword.FINAL));
        }

        int idx = typeName.indexOf('[');
        String baseType = (idx == -1 ? typeName : typeName.substring(0, idx));
        SimpleName id = new SimpleName(baseType);
        VariableDeclarator variable = new VariableDeclarator(
                new ClassOrInterfaceType(null, baseType), id);
        FieldDeclaration fd = new FieldDeclaration(modifiers, variable);
        fd.addAnnotation("javax.annotation.processing.Generated");
        return fd;
    }


    /**
     * The implicit fields divide up into two categories. Global fields
     * declared just in java.lang.Object and type specific one declared
     * in each reference type. This method adds the global ones.
     */
    private void addGlobalImplicitRecoderFields(TypeDeclaration<?> td) {
        // instance
        td.addMember(createImplicitRecoderField("boolean", IMPLICIT_INITIALIZED, false, false));
        td.addMember(createImplicitRecoderField("boolean", IMPLICIT_CREATED, false, false));
        td.addMember(createImplicitRecoderField("int", IMPLICIT_TRANSIENT, false, false));
        td.addMember(createImplicitRecoderField("boolean", IMPLICIT_TRANSACTION_UPDATED, false, false));
    }


    /**
     * adds implicit fields to the given type declaration
     *
     * @param td the recoder.java.TypeDeclaration to be enriched with
     *           implicit fields
     */
    private void addImplicitRecoderFields(TypeDeclaration<?> td) {
        td.addMember(createImplicitRecoderField("boolean", IMPLICIT_CLASS_INIT_IN_PROGRESS, true, true));
        td.addMember(createImplicitRecoderField("boolean", IMPLICIT_CLASS_ERRONEOUS, true, true));
        td.addMember(createImplicitRecoderField("boolean", IMPLICIT_CLASS_INITIALIZED, true, true));
        td.addMember(createImplicitRecoderField("boolean", IMPLICIT_CLASS_PREPARED, true, true));

        //TODO weigl not understand this
        if (td instanceof ClassOrInterfaceDeclaration &&
                (td.getName() == null || ((TypeDeclaration<?>) td).getStatementContainer() != null ||
                        td.getContainingReferenceType() != null) &&
                (containingMethod(td) == null || !containingMethod(td).isStatic()) &&
                !td.isStatic()) {
            TypeDeclaration<?> container = containingClass(td);
            String id = container.getNameAsString();
            td.addField(new ClassOrInterfaceType(null, id), IMPLICIT_ENCLOSING_THIS, Modifier.Keyword.PRIVATE);
        }
    }

    protected void addClassInitializerStatusFields(TypeDeclaration<?> td) {
        td.addMember(createImplicitRecoderField("boolean", IMPLICIT_CLASS_INIT_IN_PROGRESS, true, true));
        td.addMember(createImplicitRecoderField("boolean", IMPLICIT_CLASS_ERRONEOUS, true, true));
        td.addMember(createImplicitRecoderField("boolean", IMPLICIT_CLASS_INITIALIZED, true, true));
        td.addMember(createImplicitRecoderField("boolean", IMPLICIT_CLASS_PREPARED, true, true));
    }

    private void addFieldsForFinalVars(TypeDeclaration<?> td) {
        final List<SimpleName> vars = getLocalClass2FinalVar().get(td);
        if (vars != null) {
            // not sure why, but doing it separated in two loops is much faster (for large programs) then just in one
            // strangely, the effect is not measureable for e.g. the class init. fields...
            FieldDeclaration[] newFields = new FieldDeclaration[vars.size()];

            int i = 0;
            for (final Variable var : vars) {
                newFields[i] = createImplicitRecoderField(var.getType().getName(),
                        FINAL_VAR_PREFIX + var.getName(), false, true);
                i++;
            }

            for (final FieldDeclaration fd : newFields) {
                attach(fd, td, 0);
            }
        }
    }

    public ProblemReporter analyze() {
        javaLangObject = services.getNameInfo().getJavaLangObject();
        if (!(javaLangObject instanceof TypeDeclaration<?>)) {
            Debug.fail("Could not find class java.lang.Object or only as bytecode");
        }
        for (final TypeDeclaration cd : classDeclarations()) {
            if (cd instanceof TypeDeclaration<?> && (cd.getName() == null || ((TypeDeclaration<?>) cd).getStatementContainer() != null)) {
                (new FinalOuterVarsCollector()).walk(cd);
            }
        }
        return super.analyze();
    }

    protected void apply(TypeDeclaration<?> td) {
        addImplicitRecoderFields(td);
        addFieldsForFinalVars(td);
        if (!transformedObject && td == javaLangObject) {
            addGlobalImplicitRecoderFields(td);
            transformedObject = true;
        }
    }

}