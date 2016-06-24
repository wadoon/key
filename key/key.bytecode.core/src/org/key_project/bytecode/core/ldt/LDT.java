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

package org.key_project.bytecode.core.ldt;

import java.beans.Expression;
import java.util.Map;
import java.util.TreeMap;

import org.key_project.bytecode.core.logic.Term;
import org.key_project.bytecode.core.logic.services.BCTermServices;
import org.key_project.common.core.ldt.CC_LDT;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Named;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.program.abstraction.CCType;
import org.key_project.util.ExtList;

/**
 * An "LDT" or "language data type" class corresponds to a standard rule file
 * shipped with KeY. Usually, this rule file declares a sort (such as "int") and
 * a number of operators. The LDT class provides a programming interface to
 * access these entities, and it assists the type converter in handling them.
 * <p>
 * TODO: This class has been roughly copy-pasted from the Java version; have to
 * adjust at least some of the comments.
 */
public abstract class LDT extends CC_LDT<Term> implements Named {

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    protected LDT(Name name, BCTermServices services) {
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
    public static Map<Name, LDT> getNewLDTInstances(BCTermServices s) {

        // TreeMap ensures the map is sorted according to the natural order of
        // its keys.
        Map<Name, LDT> ret = new TreeMap<Name, LDT>();

        ret.put(IntegerLDT.NAME, new IntegerLDT(s));

        return ret;
    }

    // -------------------------------------------------------------------------
    // abstract methods
    // -------------------------------------------------------------------------

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
     *            the BCTermServices
     * @param ec
     *            the ExecutionContext in which the expression is evaluated
     * @return true if the LDT offers an operation for the given java operator
     *         and the subterm
     */
//    public abstract boolean isResponsible(
//            Instruction op,
//            Term sub,
//            BCTermServices services,
//            ExecutionContext ec);

    /**
     * returns the function symbol for the given operation
     * 
     * @return the function symbol for the given operation
     */
//    public abstract Function getFunctionFor(
//            Instruction op,
//            BCTermServices services,
//            ExecutionContext ec);

    public abstract boolean hasLiteralFunction(Function f);

    /** Is called whenever <code>hasLiteralFunction()</code> returns true. */
    public abstract Expression translateTerm(Term t, ExtList children,
            BCTermServices services);

    public abstract CCType getType(Term t);
}
