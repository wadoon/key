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

import de.uka.ilkd.key.java.transformations.InstanceAllocationMethodBuilder;
import recoder.java.Expression;
import recoder.java.Identifier;
import recoder.java.Statement;
import recoder.java.BlockStmt;
import recoder.java.declaration.*;
import recoder.java.reference.MethodReference;
import recoder.java.reference.Type;
import recoder.java.reference.VariableReference;
import recoder.java.statement.Return;
import recoder.kit.ProblemReport;
import recoder.kit.TypeKit;
import recoder.list.generic.NodeList;

import java.util.HashMap;
import java.util.LinkedHashMap;

/**
 * If an allocation expression <code>new Class(...)</code> occurs, a new object
 * has to be created, in KeY this is quite similar to take it out of a list of
 * objects and setting the implicit flag <code> &lt;created&gt; </code> to
 * <code>true</code> as well as setting all fields of the object to their
 * default values. For the complete procedure, the method creates the
 * implicit method <code>&lt;createObject$gt;</code> which on its part calls
 * another implicit method <code>lt;prepare&gt;</code> for setting the fields
 * default values.
 */
public class CreateObjectBuilder extends JavaTransformer {

    public static final String IMPLICIT_OBJECT_CREATE = "<createObject>";
    public static final String NEW_OBJECT_VAR_NAME = "__NEW__";
    private final HashMap<TypeDeclaration<?>, Identifier> class2identifier;


    public CreateObjectBuilder
            (TransformationPipelineServices services,
             TransformerCache cache) {
        super(services, cache);
        class2identifier = new LinkedHashMap<TypeDeclaration<?>, Identifier>();
    }


    /**
     * Creates the body of the static <code>&lt;createObject&gt;</code>
     * method.
     */
    private BlockStmt createBody(TypeDeclaration<?> recoderClass) {

        NodeList<Statement> result = new NodeList<Statement>(10);
        LocalVariableDeclaration local = declare(NEW_OBJECT_VAR_NAME, class2identifier.get(recoderClass));


        result.add(local);

        final NodeList<Expression> arguments = new NodeList<Expression>(0);

        result.add
                (assign(new VariableReference
                                (new Identifier(NEW_OBJECT_VAR_NAME)),
                        new MethodReference(new Type
                                (class2identifier.get(recoderClass)),
                                new ImplicitIdentifier
                                        (InstanceAllocationMethodBuilder.IMPLICIT_INSTANCE_ALLOCATE),
                                arguments)));

        MethodReference createRef =
                (new MethodReference(new VariableReference
                        (new Identifier(NEW_OBJECT_VAR_NAME)),
                        new ImplicitIdentifier
                                (CreateBuilder.IMPLICIT_CREATE)));

        // July 08 - mulbrich: wraps createRef into a method body statement to
        // avoid unnecessary dynamic dispatch.
        // Method body statement are not possible for anonymous classes, however.
        // Use a method call there
        if (recoderClass.getIdentifier() == null) {
            // anonymous
            result.add
                    (new MethodReference(new VariableReference
                            (new Identifier(NEW_OBJECT_VAR_NAME)),
                            new ImplicitIdentifier
                                    (CreateBuilder.IMPLICIT_CREATE)));
        } else {
            Type tyref;
            tyref = makeTyRef(recoderClass);
            result.add(new MethodBodyStatement(tyref, null, createRef));
        }

        // TODO why does the method return a value? Is the result ever used??
        result.add(new Return
                (new VariableReference(new Identifier(NEW_OBJECT_VAR_NAME))));

        return new BlockStmt(result);

    }

    /*
     * make a type reference. There are special classes which need to be handled
     * differently. (<Default> for instance)
     */
    private Type makeTyRef(TypeDeclaration<?> recoderClass) {
        Identifier id = recoderClass.getIdentifier();
        if (id instanceof ImplicitIdentifier)
            return new Type(id);
        else
            return TypeKit.createType(getProgramFactory(), recoderClass);
    }


    /**
     * creates the implicit static <code>&lt;createObject&gt;</code>
     * method that takes the object to be created out of the pool
     *
     * @param type the TypeDeclaration for which the
     *             <code>&lt;prepare&gt;</code> is created
     * @return the implicit <code>&lt;prepare&gt;</code> method
     */
    public MethodDeclaration createMethod(TypeDeclaration<?> type) {
        NodeList<Modifier> modifiers = new NodeList<Modifier>(2);
        modifiers.add(new Modifier(Modifier.Keyword.PUBLIC));
        modifiers.add(new Modifier(Modifier.Keyword.PUBLIC));

        MethodDeclaration md = new MethodDeclaration
                (modifiers,
                        new Type(class2identifier.get(type)),
                        new ImplicitIdentifier(IMPLICIT_OBJECT_CREATE),
                        new NodeList<Parameter>(0),
                        null,
                        createBody(type));
        md.makeAllParentRolesValid();
        return md;
    }

    public ProblemReport analyze() {
        for (final TypeDeclaration<?> cd : TypeDeclaration<?>s()) {
            class2identifier.put(cd, getId(cd));
        }
        setProblemReport(NO_PROBLEM);
        return NO_PROBLEM;
    }

    /**
     * entry method for the constructor normalform builder
     *
     * @param td the TypeDeclaration
     */
    protected void makeExplicit(TypeDeclaration td) {
        if (td instanceof TypeDeclaration<?>) {
            attach(createMethod((TypeDeclaration<?>) td), td,
                    td.getMembers().size());
//  	    java.io.StringWriter sw = new java.io.StringWriter();
//  	    services.getProgramFactory().getPrettyPrinter(sw).visitTypeDeclaration<?>((TypeDeclaration<?>)td);
//  	    System.out.println(sw.toString());
//  	    try { sw.close(); } catch (Exception e) {}		
        }
    }


}