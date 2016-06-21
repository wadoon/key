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

import java.util.Iterator;

import org.key_project.bytecode.core.logic.Term;
import org.key_project.common.core.logic.calculus.*;
import org.key_project.util.collection.ImmutableSLList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class SequentImpl extends
        CCSequentImpl<Term, SequentFormula, Semisequent, Sequent>
        implements Sequent {

    private static final Sequent EMPTY_SEQUENT = new NilSequent();

    /**
     * TODO: Document.
     *
     * @param antecedent
     * @param succedent
     */
    protected SequentImpl(Semisequent antecedent, Semisequent succedent) {
        super(antecedent, succedent);
    }

    @Override
    protected AbstractSequentFactory<Semisequent, Sequent> getSequentFactory() {
        return SequentFactory.instance();
    }

    @Override
    protected CCSequentChangeInfo<Term, SequentFormula, Semisequent, Sequent> createSequentChangeInfo(
            boolean inAntec,
            CCSemisequentChangeInfo<SequentFormula, Semisequent> semiCI,
            Sequent composeSequent, Sequent genericSequent) {
        assert semiCI instanceof SemisequentChangeInfo;

        return SequentChangeInfo.createSequentChangeInfo(inAntec,
                (SemisequentChangeInfo) semiCI, composeSequent, genericSequent);
    }

    public static Sequent nil() {
        return EMPTY_SEQUENT;
    }

    /**
     * Creates a new Sequent with empty succedent
     * 
     * @param ante
     *            the Semisequent that plays the antecedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are
     *         same as EMPTY_SEMISEQUENT
     */
    public static Sequent createAnteSequent(Semisequent ante) {
        if (ante.isEmpty()) {
            return EMPTY_SEQUENT;
        }
        return new SequentImpl(ante, SemisequentImpl.nil());
    }

    /**
     * Creates a new Sequent
     * 
     * @param ante
     *            the Semisequent that plays the antecedent part
     * @param succ
     *            the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are
     *         same as EMPTY_SEMISEQUENT
     */
    public static Sequent createSequent(Semisequent ante, Semisequent succ) {
        if (ante.isEmpty() && succ.isEmpty()) {
            return EMPTY_SEQUENT;
        }
        return new SequentImpl(ante, succ);
    }

    /**
     * Creates a new Sequent with empty antecedent
     * 
     * @param succ
     *            the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ are
     *         same as EMPTY_SEMISEQUENT
     */
    public static Sequent createSuccSequent(Semisequent succ) {
        if (succ.isEmpty()) {
            return EMPTY_SEQUENT;
        }
        return new SequentImpl(SemisequentImpl.nil(), succ);
    }

    /**
     * TODO: Document.
     *
     * @author Dominic Scheurer
     */
    static class NilSequent extends SequentImpl {

        /**
         * TODO: Document.
         *
         * @param antecedent
         * @param succedent
         */
        protected NilSequent() {
            super(SemisequentImpl.nil(), SemisequentImpl.nil());
        }

        @Override
        public boolean isEmpty() {
            return true;
        }

        @Override
        public Iterator<SequentFormula> iterator() {
            return ImmutableSLList.<SequentFormula> nil()
                    .iterator();
        }

    }

}
