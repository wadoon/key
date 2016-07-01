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

package de.uka.ilkd.key.strategy.feature.findprefix;

import org.key_project.common.core.logic.calculus.PIOPathIterator;
import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.logic.op.Operator;

import de.uka.ilkd.key.logic.Term;


/**
 * Interface for prefix checkers. Each checker is called on initialisation,
 * on every operator of the prefix starting with the outermost operator and
 * for getting the result.
 *
 * @author christoph
 */
interface Checker {

    /**
     * Called on initialisation of the prefix check.
     *
     * @param pos   the initial position of occurrence
     */
    public void initPrefixCheck(PosInOccurrence<Term> pos);


    /**
     * Called on every operator of the prefix starting with the outermost
     * operator.
     *
     * @param op   the operator to be checked
     * @param it   the prefix iterator
     */
    public void checkOperator(Operator op,
                              PIOPathIterator it);



    /**
     * Called to get the result of the prefix check.
     *
     * @param pos   the initial position of occurrence
     */
    public boolean getResult();
}