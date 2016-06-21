// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.bytecode.core.logic.calculus;

import org.key_project.bytecode.core.logic.Term;
import org.key_project.common.core.logic.calculus.CCSemisequentChangeInfo;
import org.key_project.common.core.logic.calculus.CCSequentChangeInfo;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class SequentChangeInfo extends
        CCSequentChangeInfo<Term, SequentFormula, Semisequent, Sequent> {

    /**
     * TODO: Document.
     *
     * @param antecedent
     * @param succedent
     * @param resultingSequent
     * @param originalSequent
     */
    protected SequentChangeInfo(
            CCSemisequentChangeInfo<SequentFormula, Semisequent> antecedent,
            CCSemisequentChangeInfo<SequentFormula, Semisequent> succedent,
            Sequent resultingSequent, Sequent originalSequent) {
        super(antecedent, succedent, resultingSequent, originalSequent);
    }

    /**
     * creates a new sequent change info whose semisequent described by the
     * value of the selector antec (true selects antecedent; false selects
     * succedent) has changed. The made changes are stored in semiCI and the
     * resulting sequent is given by result
     *
     * @param antec
     *            a boolean indicating if the given semisequent change
     *            information describes the changes of the antecedent or
     *            succedent
     * @param semiCI
     *            the SemisequentChangeInfo describing the changes in detail
     *            (which formulas have been added/removed)
     * @param result
     *            the Sequent which is the result of the changes
     * @param original
     *            the Sequent to which the described changes have been applied
     * @return the sequent change information object describing the complete
     *         changes made to the sequent together with the operations result.
     */
    public static SequentChangeInfo createSequentChangeInfo(boolean antec,
            SemisequentChangeInfo semiCI,
            Sequent result, Sequent original) {
        if (antec) {
            return new SequentChangeInfo(semiCI, null, result, original);
        }
        else {
            return new SequentChangeInfo(null, semiCI, result, original);
        }
    }

}
