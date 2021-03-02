// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.statement;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
 * A shortcut-statement for a method body, i.e. no dynamic dispatching any
 * longer. Used for directly embedding the body into the modality, i.e., without
 * adding a method frame.
 * <p />
 * Please take care: only the method name plus the class in which class the
 * method is implemented is part of the syntax representation of such a
 * statement, but not the methods complete syntax. If there are two methods with
 * an equal name, but different signature (i.e. parameter types), the pure
 * syntax is ambigious. In fact the concrete body this method body statement
 * represents depends on the static type of its arguments.
 * <p />
 * Therefore: Transformation of a method body statement <em>MUST</em> keep the
 * static type of the arguments <em>unchanged</em>.
 * <p />
 */
public class DirectMethodBodyStatement extends MethodBodyStatement
        implements Statement, NonTerminalProgramElement {

    /**
     * Construct a method body shortcut
     * 
     * @param bodySource exact class where the body is declared
     * @param resultVar the IProgramVariable to which the method's return value is
     * assigned
     * @param methodReference the MethodReference encapsulating the method's
     * signature
     */
    public DirectMethodBodyStatement(TypeReference bodySource, IProgramVariable resultVar,
            MethodReference methodReference) {
        super(bodySource, resultVar, methodReference);
    }

    public DirectMethodBodyStatement(ExtList list) {
        super(list);
    }

    public DirectMethodBodyStatement(IProgramMethod method, ReferencePrefix newContext,
            IProgramVariable res, ImmutableArray<Expression> args, boolean useSpecification) {
        super(method, newContext, res, args, useSpecification);
    }

    public DirectMethodBodyStatement(IProgramMethod method, ReferencePrefix newContext,
            IProgramVariable res, ImmutableArray<Expression> args, boolean useSpecification,
            ProgramElement scope) {
        super(method, newContext, res, args, useSpecification, scope);
    }


    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnDirectMethodBodyStatement(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printDirectMethodBodyStatement(this);
    }

}