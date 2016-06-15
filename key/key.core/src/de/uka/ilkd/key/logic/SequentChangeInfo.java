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

package de.uka.ilkd.key.logic;

import org.key_project.common.core.logic.calculus.SequentFormula;

/**
 * Records the changes made to a sequent. Keeps track of added and removed
 * formula to one of the semisequents. The intersection of added and removed
 * formulas of the same semisequent may not be empty, in particular this means
 * that a formula added and removed afterwards will occur in both lists. The
 * situation where this can happen is that a list of formulas had to be added to
 * the sequent and the list has not been redundance free.
 */
public class SequentChangeInfo extends GenericSequentChangeInfo<SequentFormula<JavaDLTerm>, Semisequent, Sequent> {
    /**
     * creates a new sequent change info whose semisequent described by position
     * pos has changed. The made changes are stored in semiCI and the resulting
     * sequent is given by result
     * 
     * @param pos
     *            the PosInOccurrence describing the semisequent where the
     *            changes took place
     * @param semiCI
     *            the SemisequentChangeInfo describing the changes in detail
     *            (which formulas have been added/removed)
     * @return the sequent change information object describing the complete
     *         changes made to the sequent together with the operations result.
     */
    public static SequentChangeInfo createSequentChangeInfo(
            PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pos,
            SemisequentChangeInfo semiCI,
            Sequent result, Sequent original) {
        return createSequentChangeInfo(pos.isInAntec(), semiCI, result,
                original);
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

    /**
     * creates a new sequent change info whose semisequents have changed. The
     * made changes are stored in semiCI and the resulting sequent is given by
     * result
     *
     * @param anteCI
     *            the SemisequentChangeInfo describing the changes of the
     *            antecedent in detail (which formulas have been added/removed)
     * @param sucCI
     *            the SemisequentChangeInfo describing the changes of the
     *            succedent detail (which formulas have been added/removed)
     * @return the sequent change information object describing the complete
     *         changes made to the sequent together with the operations result.
     */
    public static SequentChangeInfo createSequentChangeInfo(
            SemisequentChangeInfo anteCI, SemisequentChangeInfo sucCI,
            Sequent result, Sequent original) {
        return new SequentChangeInfo(anteCI, sucCI, result, original);
    }

    /**
     * creates a new sequent change information object. Therefore it combines
     * the changes to the semisequents of the sequent.
     * 
     * @param antecedent
     *            the SemisequentChangeInfo describing the changes of the
     *            antecedent
     * @param succedent
     *            the SemisequentChangeInfo describing the changes of the
     *            succedent
     * @param resultingSequent
     *            the Sequent being the result of the changes
     * @param originalSequent
     *            the Sequent that has been transformed
     */
    private SequentChangeInfo(SemisequentChangeInfo antecedent,
            SemisequentChangeInfo succedent, Sequent resultingSequent,
            Sequent originalSequent) {
        super(antecedent, succedent, resultingSequent, originalSequent);
    }

}