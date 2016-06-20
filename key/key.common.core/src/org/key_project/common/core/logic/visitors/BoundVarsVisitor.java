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

package org.key_project.common.core.logic.visitors;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.calculus.CCSequent;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * Visitor traversing a term and collecting all variables that occur bound. The
 * visitor implements also a continuation on sequents, traversing all of the
 * formulas occuring in the sequent.
 */
public class BoundVarsVisitor<T extends CCTerm<?, ?, T>> extends CCDefaultVisitor<T> {

    private ImmutableSet<QuantifiableVariable> bdVars =
            DefaultImmutableSet.<QuantifiableVariable> nil();

    /**
     * creates a Visitor that collects all bound variables for the subterms of
     * the term it is called from.
     */
    public BoundVarsVisitor() {
    }

    /**
     * only called by execPostOrder in Term.
     */
    public void visit(T visited) {
        for (int i = 0, ar = visited.arity(); i < ar; i++) {
            for (int j = 0, boundVarsSize =
                    visited.varsBoundHere(i).size(); j < boundVarsSize; j++) {
                bdVars = bdVars.add(visited.varsBoundHere(i).get(j));
            }
        }
    }

    /**
     * visits a sequent
     */
    public void visit(CCSequent<T, ?, ?, ?> visited) {
        for (SequentFormula<T> cf : visited) {
            visit(cf.formula());
        }
    }

    /**
     * returns all the bound variables that have been stored
     */
    public ImmutableSet<QuantifiableVariable> getBoundVariables() {
        return bdVars;
    }

}