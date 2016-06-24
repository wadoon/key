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

package de.uka.ilkd.key.ldt;

import java.util.Map;
import java.util.TreeMap;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Named;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.theories.CCTheory;
import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaDLTermServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;

/**
 * An "LDT" or "language data type" class corresponds to a standard rule file
 * shipped with KeY. Usually, this rule file declares a sort (such as "int") and
 * a number of operators. The LDT class provides a programming interface to
 * access these entities, and it assists the type converter in handling them.
 */
public abstract class LDT extends CCTheory implements Named {

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    protected LDT(Name name, JavaDLTermServices services) {
        super(name, services);
    }

    protected LDT(Name name, Sort targetSort) {
        super(name, targetSort);
    }

    // -------------------------------------------------------------------------
    // protected methods
    // -------------------------------------------------------------------------

    // -------------------------------------------------------------------------
    // public methods
    // -------------------------------------------------------------------------

    /*
     * Use this method to instantiate all LDTs. It returns a map that takes as
     * input the name of an LDT and returns an instance of the corresponding
     * LDT.
     * 
     * Is it possible to implement LDTs as singletons? (Kai Wallisch 04/2014)
     */
    public static Map<Name, LDT> getNewLDTInstances(Services s) {

        // TreeMap ensures the map is sorted according to the natural order of
        // its keys.
        Map<Name, LDT> ret = new TreeMap<Name, LDT>();

        ret.put(IntegerLDT.NAME, new IntegerLDT(s));
        ret.put(BooleanLDT.NAME, new BooleanLDT(s));
        ret.put(LocSetLDT.NAME, new LocSetLDT(s));
        ret.put(HeapLDT.NAME, new HeapLDT(s));
        ret.put(PermissionLDT.NAME, new PermissionLDT(s));
        ret.put(SeqLDT.NAME, new SeqLDT(s));
        ret.put(FreeLDT.NAME, new FreeLDT(s));
        ret.put(MapLDT.NAME, new MapLDT(s));
        ret.put(FloatLDT.NAME, new FloatLDT(s));
        ret.put(DoubleLDT.NAME, new DoubleLDT(s));
        ret.put(RealLDT.NAME, new RealLDT(s));
        ret.put(CharListLDT.NAME, new CharListLDT(s));

        return ret;
    }

    // -------------------------------------------------------------------------
    // abstract methods
    // -------------------------------------------------------------------------

    /**
     * returns true if the LDT offers an operation for the given java operator
     * and the logic subterms
     * 
     * @param op
     *            the org.key_project.common.core.services.expression.Operator
     *            to translate
     * @param subs
     *            the logic subterms of the java operator
     * @param services
     *            the Services
     * @param ec
     *            the ExecutionContext in which the expression is evaluated
     * @return true if the LDT offers an operation for the given java operator
     *         and the subterms
     */
    public abstract boolean isResponsible(
            de.uka.ilkd.key.java.expression.Operator op,
            Term[] subs,
            Services services,
            ExecutionContext ec);

    /**
     * returns true if the LDT offers an operation for the given binary java
     * operator and the logic subterms
     * 
     * @param op
     *            the org.key_project.common.core.services.expression.Operator
     *            to translate
     * @param left
     *            the left subterm of the java operator
     * @param right
     *            the right subterm of the java operator
     * @param services
     *            the Services
     * @param ec
     *            the ExecutionContext in which the expression is evaluated
     * @return true if the LDT offers an operation for the given java operator
     *         and the subterms
     */
    public abstract boolean isResponsible(
            de.uka.ilkd.key.java.expression.Operator op,
            Term left,
            Term right,
            Services services, ExecutionContext ec);

    /**
     * returns true if the LDT offers an operation for the given unary java
     * operator and the logic subterms
     * 
     * @param op
     *            the org.key_project.common.core.services.expression.Operator
     *            to translate
     * @param sub
     *            the logic subterms of the java operator
     * @param services
     *            the Services
     * @param ec
     *            the ExecutionContext in which the expression is evaluated
     * @return true if the LDT offers an operation for the given java operator
     *         and the subterm
     */
    public abstract boolean isResponsible(
            de.uka.ilkd.key.java.expression.Operator op,
            Term sub,
            JavaDLTermServices services,
            ExecutionContext ec);

    /**
     * translates a given literal to its logic counterpart
     * 
     * @param lit
     *            the Literal to be translated
     * @return the Term that represents the given literal in its logic form
     */
    public abstract Term translateLiteral(Literal lit, Services services);

    /**
     * returns the function symbol for the given operation
     * 
     * @return the function symbol for the given operation
     */
    public abstract Function getFunctionFor(
            de.uka.ilkd.key.java.expression.Operator op,
            Services services,
            ExecutionContext ec);

    public abstract boolean hasLiteralFunction(Function f);

    /** Is called whenever <code>hasLiteralFunction()</code> returns true. */
    public abstract Expression translateTerm(Term t, ExtList children,
            Services services);

    
    public abstract Type getType(Term t);
}
