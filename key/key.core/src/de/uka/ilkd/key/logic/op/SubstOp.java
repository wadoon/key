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

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;

/**
 * Standard first-order substitution operator, resolving clashes but not
 * preventing (usually unsound) substitution of non-rigid terms across modal
 * operators. Currently, only the subclass <code>WarySubstOp</code> is used and
 * accessible through the key parser.
 */
public abstract class SubstOp extends AbstractOperator {

    protected SubstOp(Name name) {
        super(name, 2, new Boolean[] { false, true }, true);
    }

    /**
     * Apply this substitution operator to <code>term</code>, which has this
     * operator as top-level operator
     * 
     * @param services
     *            TODO
     */
    public abstract Term apply(Term term, TermServices services);// {
    // QuantifiableVariable v =
    // term.varsBoundHere(1).getQuantifiableVariable(0);
    // ClashFreeSubst cfSubst = new ClashFreeSubst(v, term.sub(0));
    // Term res = cfSubst.apply(term.sub(1));
    // return res;
    // }
}