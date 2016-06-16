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

import java.util.Iterator;

import org.key_project.common.core.logic.calculus.AbstractSequentFactory;
import org.key_project.common.core.logic.calculus.CCSemisequentChangeInfo;
import org.key_project.common.core.logic.calculus.CCSequent;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableSLList;

/**
 * This class represents a sequent. A sequent consists of an antecedent and
 * succedent. As a sequent is persistent there is no public constructor.
 * <p>
 * A sequent is created either by using one of the composition methods, that are
 * {@link Sequent#createSequent}, {@link Sequent#createAnteSequent} and
 * {@link Sequent#createSuccSequent} or by inserting formulas directly into
 * {@link Sequent#EMPTY_SEQUENT}.
 */
public class Sequent
        extends
        CCSequent<JavaDLTerm, SequentFormula<JavaDLTerm>, Semisequent, Sequent>
        implements Iterable<SequentFormula<JavaDLTerm>> {

    public static final Sequent EMPTY_SEQUENT = new NILSequent();

    /**
     * creates a new Sequent with empty succedent
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
        return new Sequent(ante, Semisequent.nil());
    }

    /**
     * creates a new Sequent
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
        return new Sequent(ante, succ);
    }

    /**
     * creates a new Sequent with empty antecedent
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
        return new Sequent(Semisequent.nil(), succ);
    }

    /** creates new Sequent with antecedent and succedent */
    Sequent(Semisequent antecedent, Semisequent succedent) {
        super(antecedent, succedent);
    }

    static class NILSequent extends Sequent {

        /**
         * TODO: Document.
         *
         * @param antecedent
         * @param succedent
         */
        NILSequent() {
            super(Semisequent.nil(), Semisequent.nil());
        }

        public boolean isEmpty() {
            return true;
        }

        public Iterator<SequentFormula<JavaDLTerm>> iterator() {
            return ImmutableSLList.<SequentFormula<JavaDLTerm>> nil()
                    .iterator();
        }

        public boolean varIsBound(QuantifiableVariable v) {
            return false;
        }

    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.logic.GenericSequent#getSequentFactory()
     */
    @Override
    protected AbstractSequentFactory<Semisequent, Sequent> getSequentFactory() {
        return SequentFactory.instance();
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.key.logic.GenericSequent#createSequentChangeInfo(boolean,
     * de.uka.ilkd.key.logic.GenericSemisequentChangeInfo,
     * de.uka.ilkd.key.logic.GenericSequent,
     * de.uka.ilkd.key.logic.GenericSequent)
     */
    @Override
    protected SequentChangeInfo createSequentChangeInfo(
            boolean inAntec,
            CCSemisequentChangeInfo<SequentFormula<JavaDLTerm>, Semisequent> semiCI,
            Sequent result, Sequent original) {
        assert semiCI instanceof SemisequentChangeInfo;

        return SequentChangeInfo.createSequentChangeInfo(inAntec,
                (SemisequentChangeInfo) semiCI, result, original);
    }
}