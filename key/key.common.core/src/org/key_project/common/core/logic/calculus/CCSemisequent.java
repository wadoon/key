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

import org.key_project.common.core.logic.CCTerm;
import org.key_project.util.collection.ImmutableList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 * @param <SeqFor>
 * @param <SemiSeq>
 */
public interface CCSemisequent<T extends CCTerm<?, ?, ?, T>, SemiSeq extends CCSemisequent<T, SemiSeq>>
        extends Iterable<SequentFormula<T>> {

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
    CCSemisequentChangeInfo<T, SemiSeq> insert(
            int idx, SequentFormula<T> sequentFormula);

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
    CCSemisequentChangeInfo<T, SemiSeq> insert(
            int idx, Iterable<SequentFormula<T>> insertionList);

    /**
     * inserts element at index 0 performing redundancy checks, this may result
     * in returning same semisequent if inserting would create redundancies
     * 
     * @param sequentFormula
     *            SeqFor to be inserted
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    CCSemisequentChangeInfo<T, SemiSeq> insertFirst(
            SequentFormula<T> sequentFormula);

    /**
     * inserts element at index 0 performing redundancy checks, this may result
     * in returning same semisequent if inserting would create redundancies
     * 
     * @param insertions
     *            IList<SeqFor> to be inserted
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    CCSemisequentChangeInfo<T, SemiSeq> insertFirst(
            Iterable<SequentFormula<T>> insertions);

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
    CCSemisequentChangeInfo<T, SemiSeq> insertLast(
            SequentFormula<T> sequentFormula);

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
    CCSemisequentChangeInfo<T, SemiSeq> insertLast(
            Iterable<SequentFormula<T>> insertions);

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
     *            the PosInOccurrence<Term, SequentFormula<T><Term>>
     *            describing the position of and within the formula below which
     *            the formula differs from the new formula
     *            <code>sequentFormula</code>
     * @param sequentFormula
     *            the SeqFor replacing the old element at index idx
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    CCSemisequentChangeInfo<T, SemiSeq> replace(
            PosInOccurrence<T> pos, SequentFormula<T> sequentFormula);

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
    CCSemisequentChangeInfo<T, SemiSeq> replace(
            int idx, SequentFormula<T> sequentFormula);

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
    CCSemisequentChangeInfo<T, SemiSeq> replace(
            PosInOccurrence<T> pos, Iterable<SequentFormula<T>> replacements);

    CCSemisequentChangeInfo<T, SemiSeq> replace(
            int idx, Iterable<SequentFormula<T>> replacements);

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
    CCSemisequentChangeInfo<T, SemiSeq> remove(int idx);

    /**
     * returns the index of the given {@link SeqFor} or {@code -1} if the
     * sequent formula is not found. Equality of sequent formulas is checked
     * sing the identy check (i.e.,{@link ==})
     * 
     * @param sequentFormula
     *            the {@link SeqFor} to look for
     * @return index of sequentFormula (-1 if not found)
     */
    int indexOf(SequentFormula<T> sequentFormula);

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
    SequentFormula<T> get(int idx);

    /** @return the first {@link SeqFor} of this Semisequent */
    SequentFormula<T> getFirst();

    /**
     * checks if the {@link SeqFor} occurs in this Semisequent (identity check)
     * 
     * @param sequentFormula
     *            the {@link SeqFor} to look for
     * @return true iff. sequentFormula has been found in this Semisequent
     */
    boolean contains(SequentFormula<T> sequentFormula);

    /**
     * checks if a {@link SeqFor} is in this Semisequent (equality check)
     * 
     * @param sequentFormula
     *            the {@link SeqFor} to look for
     * @return true iff. sequentFormula has been found in this Semisequent
     */
    boolean containsEqual(SequentFormula<T> sequentFormula);

    ImmutableList<SequentFormula<T>> asList();

}