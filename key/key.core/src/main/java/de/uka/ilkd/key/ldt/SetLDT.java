// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.ldt;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;

/**
 * A simple {@link LDT} for unsorted sets.
 *
 * @author Dominic Steinhoefel
 */
public final class SetLDT extends LDT {

    public static final Name NAME = new Name("Set");

    private final Function empty;
    private final Function singleton;
    private final Function union;

    public SetLDT(TermServices services) {
        super(NAME, services);
        empty = addFunction(services, "setEmpty");
        singleton = addFunction(services, "setSingleton");
        union = addFunction(services, "setUnion");
    }

    public Function getEmpty() {
        return empty;
    }

    public Function getSingleton() {
        return singleton;
    }

    public Function getUnion() {
        return union;
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
            Term[] subs, Services services, ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
            Term left, Term right, Services services, ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
            Term sub, TermServices services, ExecutionContext ec) {
        return false;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
        assert false;
        return null;
    }

    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op,
            Services serv, ExecutionContext ec) {
        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return false;
    }

    @Override
    public Expression translateTerm(Term t, ExtList children,
            Services services) {
        assert false;
        return null;
    }

    @Override
    public final Type getType(Term t) {
        assert false;
        return null;
    }
}