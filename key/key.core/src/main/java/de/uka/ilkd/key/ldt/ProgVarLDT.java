// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
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
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.operator.adt.SingletonPVFun;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * An {@link LDT} for using \progvar in JML. This allows to define framing
 * conditions with progrma variables, like "\forall \progvar pv", etc. We need
 * this to refer to the ProgVar sort.
 * 
 * @author Dominic Steinhoefel
 */
public class ProgVarLDT extends LDT {
    public final static Name NAME = new Name("ProgVar");

    private final Sort progVarSort;
    private final Function pvConstructor;

    public ProgVarLDT(TermServices services) {
        super(NAME, services);
        final Namespace<Sort> sorts = services.getNamespaces().sorts();

        progVarSort = sorts.lookup(new Name("ProgVar"));
        pvConstructor = addFunction(services, "PV");
    }

    public Sort getProgVarSort() {
        return progVarSort;
    }

    public Function getPvConstructor() {
        return pvConstructor;
    }

    @Override
    public boolean isResponsible(Operator op, Term[] subs, Services services, ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term left, Term right, Services services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term sub, TermServices services,
            ExecutionContext ec) {
        return op instanceof SingletonPVFun;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
        return null;
    }

    @Override
    public Function getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        if (op instanceof SingletonPVFun) {
            return pvConstructor;
        }
        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return false;
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        return null;
    }

    @Override
    public Type getType(Term t) {
        return null;
    }
}
