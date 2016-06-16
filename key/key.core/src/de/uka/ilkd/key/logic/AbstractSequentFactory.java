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


/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public abstract class AbstractSequentFactory<SemiSeq extends GenericSemisequent<?, ?>, Seq extends GenericSequent<?, ?, ?, ?>> {

    /**
     * TODO: Document.
     *
     */
    public AbstractSequentFactory() {
        super();
    }

        /**
         * creates a new GenericSequent<T, SeqFor> with empty succedent 
         * @param ante the GenericSemisequent<T, SeqFor> that plays the antecedent part
         * @return the new sequent or the EMPTY_SEQUENT if both antec and succ
         * are same as EMPTY_SEMISEQUENT
         */
    public abstract Seq createSuccSequent(SemiSeq succ);

    /**
     * creates a new GenericSequent<T, SeqFor> 
     * @param ante the GenericSemisequent<T, SeqFor> that plays the antecedent part
     * @param succ the GenericSemisequent<T, SeqFor> that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ
     * are same as EMPTY_SEMISEQUENT
     */
    public abstract Seq createSequent(SemiSeq ante, SemiSeq succ);

    /**
     * creates a new GenericSequent<T, SeqFor> with empty antecedent 
     * @param succ the GenericSemisequent<T, SeqFor> that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ
     * are same as EMPTY_SEMISEQUENT
     */
    public abstract Seq createAnteSequent(SemiSeq succ);
    
    public abstract Seq nil();
 
}