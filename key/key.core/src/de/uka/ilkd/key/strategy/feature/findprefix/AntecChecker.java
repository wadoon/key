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
 * Checks, whether the position in occurrence is in the antecedent.
 * 
 * @author christoph
 */
class AntecChecker implements Checker {
    private boolean isInAntec;

    @Override
    public void initPrefixCheck(PosInOccurrence<Term> p_pos) {
        isInAntec = p_pos.isInAntec();
    }


    @Override
    public void checkOperator(Operator op,
                              PIOPathIterator<Term> it) {
        // do nothing
    }


    @Override
    public boolean getResult() {
        return isInAntec;
    }

}