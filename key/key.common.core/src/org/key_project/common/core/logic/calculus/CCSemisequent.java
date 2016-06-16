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

package org.key_project.common.core.logic.calculus;

import org.key_project.util.collection.ImmutableList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 * @param <SeqFor>
 * @param <SemiSeq>
 */
public interface CCSemisequent<SeqFor extends SequentFormula<?>, SemiSeq extends CCSemisequent<SeqFor, SemiSeq>>
        extends Iterable<SeqFor> {

    /**
     * inserts an element at a specified index performing redundancy checks,
     * this may result in returning same semisequent if inserting would create
     * redundancies
     * 
     * @param idx
     *            int encoding the place the element has to be put
     * @param sequentFormula
     *            {@link SeqFor} to be inserted
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    CCSemisequentChangeInfo<SeqFor, SemiSeq> insert(
            int idx, SeqFor sequentFormula);

    /**
     * inserts the elements of the list at the specified index performing
     * redundancy checks
     * 
     * @param idx
     *            int encoding the place where the insertion starts
     * @param insertionList
     *            IList<SeqFor> to be inserted starting at idx
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    CCSemisequentChangeInfo<SeqFor, SemiSeq> insert(
            int idx, ImmutableList<SeqFor> insertionList);

    /**
     * inserts element at index 0 performing redundancy checks, this may result
     * in returning same semisequent if inserting would create redundancies
     * 
     * @param sequentFormula
     *            SeqFor to be inserted
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    CCSemisequentChangeInfo<SeqFor, SemiSeq> insertFirst(
            SeqFor sequentFormula);

    /**
     * inserts element at index 0 performing redundancy checks, this may result
     * in returning same semisequent if inserting would create redundancies
     * 
     * @param insertions
     *            IList<SeqFor> to be inserted
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    CCSemisequentChangeInfo<SeqFor, SemiSeq> insertFirst(
            ImmutableList<SeqFor> insertions);

    /**
     * inserts element at the end of the semisequent performing redundancy
     * checks, this may result in returning same semisequent if inserting would
     * create redundancies
     * 
     * @param sequentFormula
     *            {@link SeqFor} to be inserted
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    CCSemisequentChangeInfo<SeqFor, SemiSeq> insertLast(
            SeqFor sequentFormula);

    /**
     * inserts the formulas of the list at the end of the semisequent performing
     * redundancy checks, this may result in returning same semisequent if
     * inserting would create redundancies
     * 
     * @param insertions
     *            the IList<SeqFor> to be inserted
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    CCSemisequentChangeInfo<SeqFor, SemiSeq> insertLast(
            ImmutableList<SeqFor> insertions);

    /**
     * is this a semisequent that contains no formulas
     * 
     * @return true if the semisequent contains no formulas
     */
    boolean isEmpty();

    /**
     * replaces the element at place idx with sequentFormula
     * 
     * @param pos
     *            the PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>
     *            describing the position of and within the formula below which
     *            the formula differs from the new formula
     *            <code>sequentFormula</code>
     * @param sequentFormula
     *            the SeqFor replacing the old element at index idx
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    CCSemisequentChangeInfo<SeqFor, SemiSeq> replace(
            PosInOccurrence<?, SeqFor> pos, SeqFor sequentFormula);

    /**
     * replaces the <tt>idx</tt>-th formula by <tt>sequentFormula</tt>
     * 
     * @param idx
     *            the int with the position of the formula to be replaced
     * @param sequentFormula
     *            the SeqFor replacing the formula at the given position
     * @return a SemisequentChangeInfo containing the new sequent and a diff to
     *         the old one
     */
    CCSemisequentChangeInfo<SeqFor, SemiSeq> replace(
            int idx, SeqFor sequentFormula);

    /**
     * replaces the element at place idx with the first element of the given
     * list and adds the rest of the list to the semisequent behind the replaced
     * formula
     * 
     * @param pos
     *            the formula to be replaced
     * @param replacements
     *            the IList<SeqFor> whose head replaces the element at index idx
     *            and the tail is added to the semisequent
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    CCSemisequentChangeInfo<SeqFor, SemiSeq> replace(
            PosInOccurrence<?, SeqFor> pos, ImmutableList<SeqFor> replacements);

    CCSemisequentChangeInfo<SeqFor, SemiSeq> replace(
            int idx, ImmutableList<SeqFor> replacements);

    /** @return int counting the elements of this semisequent */
    int size();

    /**
     * removes an element
     * 
     * @param idx
     *            int being the index of the element that has to be removed
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    CCSemisequentChangeInfo<SeqFor, SemiSeq> remove(int idx);

    /**
     * returns the index of the given {@link SeqFor} or {@code -1} if the
     * sequent formula is not found. Equality of sequent formulas is checked
     * sing the identy check (i.e.,{@link ==})
     * 
     * @param sequentFormula
     *            the {@link SeqFor} to look for
     * @return index of sequentFormula (-1 if not found)
     */
    int indexOf(SeqFor sequentFormula);

    /**
     * gets the element at a specific index
     * 
     * @param idx
     *            int representing the index of the element we want to have
     * @return {@link SeqFor} found at index idx
     * @throws IndexOutOfBoundsException
     *             if idx is negative or greater or equal to
     *             {@link Sequent#size()}
     */
    SeqFor get(int idx);

    /** @return the first {@link SeqFor} of this Semisequent */
    SeqFor getFirst();

    /**
     * checks if the {@link SeqFor} occurs in this Semisequent (identity check)
     * 
     * @param sequentFormula
     *            the {@link SeqFor} to look for
     * @return true iff. sequentFormula has been found in this Semisequent
     */
    boolean contains(SeqFor sequentFormula);

    /**
     * checks if a {@link SeqFor} is in this Semisequent (equality check)
     * 
     * @param sequentFormula
     *            the {@link SeqFor} to look for
     * @return true iff. sequentFormula has been found in this Semisequent
     */
    boolean containsEqual(SeqFor sequentFormula);

    ImmutableList<SeqFor> asList();

}