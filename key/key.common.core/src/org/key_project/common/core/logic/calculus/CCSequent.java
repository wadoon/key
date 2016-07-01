package org.key_project.common.core.logic.calculus;

import java.util.Set;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.Name;

public interface CCSequent<T extends CCTerm<?, ?, ?, T>,
        SemiSeq extends CCSemisequent<T, SemiSeq>, Seq extends CCSequent<T, SemiSeq, Seq>>
          extends Iterable<SequentFormula<T>>{

    /**
     * adds a formula to the antecedent (or succedent) of the sequent. Depending
     * on the value of first the formulas are inserted at the beginning or end
     * of the ante-/succedent. (NOTICE:GenericSequent<T, SeqFor> determines
     * index using identy (==) not equality.)
     * 
     * @param cf
     *            the SeqFor to be added
     * @param antec
     *            boolean selecting the correct semisequent where to insert the
     *            formulas. If set to true, the antecedent is taken otherwise
     *            the succedent.
     * @param first
     *            boolean if true the formula is added at the beginning of the
     *            ante-/succedent, otherwise to the end
     * @return a GenericSequentChangeInfo<SeqFor, SemiSeq, Seq> which contains
     *         the new sequent and information which formulas have been added or
     *         removed
     */
    CCSequentChangeInfo<T, Seq> addFormula(SequentFormula<T> cf,
                                           boolean antec, boolean first);

    /**
     * adds a formula to the sequent at the given position.
     * (NOTICE:GenericSequent<T, SeqFor> determines index using identy (==) not
     * equality.)
     * 
     * @param cf
     *            a SeqFor to be added
     * @param p
     *            a PosInOccurrence<T, SeqFor> describes position in the sequent
     * @return a GenericSequentChangeInfo<SeqFor, SemiSeq, Seq> which contains
     *         the new sequent and information which formulas have been added or
     *         removed
     */
    CCSequentChangeInfo<T, Seq> addFormula(SequentFormula<T> cf,
                                           PosInOccurrence<T> p);

    /**
     * adds list of formulas to the antecedent (or succedent) of the sequent.
     * Depending on the value of first the formulas are inserted at the
     * beginning or end of the ante-/succedent. (NOTICE:GenericSequent<T,
     * SeqFor> determines index using identity (==) not equality.)
     * 
     * @param insertions
     *            the IList<SeqFor> to be added
     * @param antec
     *            boolean selecting the correct semisequent where to insert the
     *            formulas. If set to true, the antecedent is taken otherwise
     *            the succedent.
     * @param first
     *            boolean if true the formulas are added at the beginning of the
     *            ante-/succedent, otherwise to the end
     * @return a GenericSequentChangeInfo<SeqFor, SemiSeq, Seq> which contains
     *         the new sequent and information which formulas have been added or
     *         removed
     */
    CCSequentChangeInfo<T, Seq> addFormula(
            Iterable<SequentFormula<T>> insertions, boolean antec, boolean first);

    /**
     * adds the formulas of list insertions to the sequent starting at position
     * p. (NOTICE:GenericSequent<T, SeqFor> determines index using identy (==)
     * not equality.)
     * 
     * @param insertions
     *            a {@link Iterable} of SeqFor with the formulas to be added
     * @param p
     *            the PosInOccurrence<T, SeqFor> describing the position where
     *            to insert the formulas
     * @return a GenericSequentChangeInfo<SeqFor, SemiSeq, Seq> which contains
     *         the new sequent and information which formulas have been added or
     *         removed
     */
    CCSequentChangeInfo<T, Seq> addFormula(
            Iterable<SequentFormula<T>> insertions, PosInOccurrence<T> p);

    /** returns semisequent of the antecedent to work with */
    SemiSeq antecedent();

    /**
     * replaces the formula at the given position with another one
     * (NOTICE:GenericSequent<T, SeqFor> determines index using identity (==)
     * not equality.)
     * 
     * @param newCF
     *            the SeqFor replacing the old one
     * @param p
     *            a PosInOccurrence<T, SeqFor> describes position in the sequent
     * @return a GenericSequentChangeInfo<SeqFor, SemiSeq, Seq> which contains
     *         the new sequent and information which formulas have been added or
     *         removed
     */
    CCSequentChangeInfo<T, Seq> changeFormula(SequentFormula<T> newCF,
                                              PosInOccurrence<T> p);

    /**
     * replaces the formula at position p with the head of the given list and
     * adds the remaining list elements to the sequent (NOTICE:GenericSequent<T,
     * SeqFor> determines index using identity (==) not equality.)
     * 
     * @param replacements
     *            the {@link Iterable} of sequent formulas whose head replaces the formula at position
     *            p and adds the rest of the list behind the changed formula
     * @param p
     *            a PosInOccurrence<T, SeqFor> describing the position of the
     *            formula to be replaced
     * @return a GenericSequentChangeInfo<SeqFor, SemiSeq, Seq> which contains
     *         the new sequent and information which formulas have been added or
     *         removed
     */
    CCSequentChangeInfo<T, Seq> changeFormula(
            Iterable<SequentFormula<T>> replacements, PosInOccurrence<T> p);

    /**
     * determines if the sequent is empty.
     * 
     * @return true iff the sequent consists of two instances of
     *         GenericSemisequent<SeqFor, SemiSeq>.EMPTY_SEMISEQUENT
     */
    boolean isEmpty();

    int formulaNumberInSequent(boolean inAntec, SequentFormula<T> cfma);

    SequentFormula<T> getFormulabyNr(int formulaNumber);

    boolean numberInAntec(int formulaNumber);

    /**
     * removes the formula at position p (NOTICE:GenericSequent<T, SeqFor>
     * determines index using identity (==) not equality.)
     * 
     * @param p
     *            a PosInOccurrence<T, SeqFor> that describes position in the
     *            sequent
     * @return a GenericSequentChangeInfo<SeqFor, SemiSeq, Seq> which contains
     *         the new sequent and information which formulas have been added or
     *         removed
     */
    CCSequentChangeInfo<T, Seq> removeFormula(
            PosInOccurrence<T> p);

    int size();

    /** returns semisequent of the succedent to work with */
    SemiSeq succedent();

    /*
     * Returns names of TermLabels, that occur in this sequent.
     */
    Set<Name> getOccuringTermLabels();

}