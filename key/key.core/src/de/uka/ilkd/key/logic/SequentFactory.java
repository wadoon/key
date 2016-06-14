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

package de.uka.ilkd.key.logic;

import org.key_project.common.core.logic.calculus.SequentFormula;


/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class SequentFactory extends AbstractSequentFactory<Semisequent, Sequent> {    
    /**
     * creates a new GenericSequent<T, SeqFor> with empty succedent 
     * @param ante the GenericSemisequent<T, SeqFor> that plays the antecedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ
     * are same as EMPTY_SEMISEQUENT
     */
    @Override
    public Sequent createAnteSequent(Semisequent ante) {
        if (ante.isEmpty()) {
            return (Sequent) GenericSequent.EMPTY_SEQUENT;
        }
        return createSequent(ante, GenericSemisequent.<JavaDLTerm, SequentFormula<JavaDLTerm>, Semisequent>nil());
    }

    /**
     * creates a new GenericSequent<T, SeqFor> 
     * @param ante the GenericSemisequent<T, SeqFor> that plays the antecedent part
     * @param succ the GenericSemisequent<T, SeqFor> that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ
     * are same as EMPTY_SEMISEQUENT
     */
    @Override
    public Sequent createSequent(Semisequent ante, Semisequent succ) {
        if (ante.isEmpty() && succ.isEmpty()) {
            return (Sequent) GenericSequent.EMPTY_SEQUENT;
        }
        return Sequent.createSequent(ante, succ);
    }

    /**
     * creates a new GenericSequent<T, SeqFor> with empty antecedent 
     * @param succ the GenericSemisequent<T, SeqFor> that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ
     * are same as EMPTY_SEMISEQUENT
     */
    @Override
    public Sequent createSuccSequent(Semisequent succ) {
        if (succ.isEmpty()) {
            return (Sequent) GenericSequent.EMPTY_SEQUENT;
        }
        return createSequent(GenericSemisequent.<JavaDLTerm, SequentFormula<JavaDLTerm>, Semisequent>nil(), succ);
    }



}
