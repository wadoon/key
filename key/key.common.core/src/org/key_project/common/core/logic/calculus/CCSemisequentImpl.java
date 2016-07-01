package org.key_project.common.core.logic.calculus;

import java.util.*;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 * @param <SeqFor>
 * @param <SemiSeq>
 */
public abstract class CCSemisequentImpl<T extends CCTerm<?, ?, ?, T>, SemiSeq extends CCSemisequent<T, SemiSeq>> implements CCSemisequent<T, SemiSeq> {

    /** list with the {@link SequentFormula<T>}s of the Semisequent */
    protected final ImmutableList<SequentFormula<T>> seqList;

    protected abstract CCSemisequentChangeInfo<T, SemiSeq> createSemisequentChangeInfo(
            ImmutableList<SequentFormula<T>> formulas);

    /** used by inner class Empty */
    protected CCSemisequentImpl() {
        seqList = ImmutableSLList.<SequentFormula<T>> nil();
    }

    /**
     * creates a new Semisequent with the Semisequent elements in seqList; the
     * provided list must be redundance free, i.e., the created sequent must be
     * exactly the same as when creating the sequent by subsequently inserting
     * all formulas
     */
    protected CCSemisequentImpl(ImmutableList<SequentFormula<T>> seqList) {
        assert !seqList.isEmpty();
        this.seqList = seqList;
    }

    /**
     * creates a new Semisequent with the Semisequent elements in seqList
     */
    public CCSemisequentImpl(SequentFormula<T> seqFormula) {
        assert seqFormula != null;
        this.seqList = ImmutableSLList.<SequentFormula<T>> nil().append(seqFormula);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#insert(int, SeqFor)
     */
    @Override
    public CCSemisequentChangeInfo<T, SemiSeq> insert(
            int idx, SequentFormula<T> sequentFormula) {
        return removeRedundance(idx, sequentFormula);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#insert(int, org.key_project.util.collection.ImmutableList)
     */
    @Override
    public CCSemisequentChangeInfo<T, SemiSeq> insert(
            int idx, Iterable<SequentFormula<T>> insertionList) {
        return removeRedundance(idx, insertionList);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#insertFirst(SeqFor)
     */
    @Override
    public CCSemisequentChangeInfo<T, SemiSeq> insertFirst(
            SequentFormula<T> sequentFormula) {
        return insert(0, sequentFormula);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#insertFirst(org.key_project.util.collection.ImmutableList)
     */
    @Override
    public CCSemisequentChangeInfo<T, SemiSeq> insertFirst(
            Iterable<SequentFormula<T>> insertions) {
        return insert(0, insertions);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#insertLast(SeqFor)
     */
    @Override
    public CCSemisequentChangeInfo<T, SemiSeq> insertLast(
            SequentFormula<T> sequentFormula) {
        return insert(size(), sequentFormula);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#insertLast(org.key_project.util.collection.ImmutableList)
     */
    @Override
    public CCSemisequentChangeInfo<T, SemiSeq> insertLast(
            Iterable<SequentFormula<T>> insertions) {
        return insert(size(), insertions);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return seqList.isEmpty();
    }
    
    /**
     * Creates a list from a given {@link Iterable}.
     * <p>
     * TODO: Should be a member of {@link ImmutableList}.
     *
     * @param it The {@link Iterable} to transform.
     * @return A list with the elements of the {@link Iterable}.
     */
    private static <T> List<T> toList(Iterable<T> it) {
        final ArrayList<T> result = new ArrayList<T>();
        for (T elem : it) {
            result.add(elem);
        }
        return result;
    }
    
    /**
     * Inserts new SeqFor at index idx and removes duplicates.
     *
     * @param idx
     * @param sequentFormula
     * @param semiSeqCI
     * @param fci null if the formula to be added is new, otherwise an object
     *            telling which formula is replaced with the new formula
     *            <code>sequentFormula</code>, and what are the differences
     *            between the two formulas
     * @return a {@link CCSemisequentChangeInfo} object with the new semisequent
     *         and information about which formulas have been added or removed
     */
    private CCSemisequentChangeInfo<T, SemiSeq> insertAndRemoveRedundancyHelper(
            int idx,
            SequentFormula<T> sequentFormula,
            CCSemisequentChangeInfo<T, SemiSeq> semiSeqCI,
            FormulaChangeInfo<T> fci) {

        // Search for equivalent formulas
        for (SequentFormula<T> formula : semiSeqCI.getFormulaList()) {
            if (sequentFormula != null
                    && formula.formula().equalsModRenaming(sequentFormula.formula())) {

                semiSeqCI.rejectedFormula(sequentFormula);
                return semiSeqCI; // semisequent already contains formula
            }
        }
        
        final List<SequentFormula<T>> existingFormulas = toList(semiSeqCI.getFormulaList());
        ImmutableList<SequentFormula<T>> newFormulaList = ImmutableSLList.<SequentFormula<T>>nil();
        
        if (fci == null) {
            semiSeqCI.addedFormula(idx, sequentFormula);
        } else {
            semiSeqCI.modifiedFormula(idx, fci);
        }
        
        // Border cases: Empty semisequent or addition at the end
        if (existingFormulas.isEmpty() || idx >= existingFormulas.size()) {
            newFormulaList = newFormulaList.prepend(sequentFormula);
        }
        
        for (int i = existingFormulas.size() - 1; i >= 0; i--) {
            newFormulaList = newFormulaList.prepend(existingFormulas.get(i));

            if (idx == i) {
                newFormulaList = newFormulaList.prepend(sequentFormula);
            }
        }

        // add new formula list to result object
        semiSeqCI.setFormulaList(newFormulaList);

        return semiSeqCI;
    }

    /**
     * . inserts new ConstrainedFormulas starting at index idx and removes
     * duplicates, perform simplifications etc.
     * 
     * @param sequentFormulasToBeInserted
     *            the {@link Iterable<SeqFor>} to be inserted at position
     *            idx
     * @param idx
     *            an int that means insert sequentFormula at the idx-th position
     *            in the semisequent
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    private CCSemisequentChangeInfo<T, SemiSeq> insertAndRemoveRedundancy(
            int idx,
            Iterable<SequentFormula<T>> sequentFormulasToBeInserted,
            CCSemisequentChangeInfo<T, SemiSeq> sci) {

        int pos = idx;
        ImmutableList<SequentFormula<T>> oldFormulas = sci.getFormulaList();

        for (SequentFormula<T> aSequentFormula : sequentFormulasToBeInserted) {
            sci = insertAndRemoveRedundancyHelper(pos, aSequentFormula, sci,
                            null);

            if (sci.getFormulaList() != oldFormulas) {
                pos = sci.getIndex() + 1;
                oldFormulas = sci.getFormulaList();
            }
        }
        return sci;
    }

    /**
     * . inserts new ConstrainedFormulas starting at index idx and removes
     * duplicates, perform simplifications etc.
     * 
     * @param sequentFormula
     *            the IList<SeqFor> to be inserted at position idx
     * @param idx
     *            an int that means insert sequentFormula at the idx-th position
     *            in the semisequent
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    private CCSemisequentChangeInfo<T, SemiSeq> removeRedundance(
            int idx, Iterable<SequentFormula<T>> sequentFormula) {
        return insertAndRemoveRedundancy(idx, sequentFormula,
                createSemisequentChangeInfo(seqList));
    }

    /**
     * . inserts new SeqFor at index idx and removes duplicates, perform
     * simplifications etc.
     * 
     * @param sequentFormula
     *            the SeqFor to be inserted at position idx
     * @param idx
     *            an int that means insert sequentFormula at the idx-th position
     *            in the semisequent
     * @return new Semisequent with sequentFormula at index idx and removed
     *         redundancies
     */
    private CCSemisequentChangeInfo<T, SemiSeq> removeRedundance(
            int idx, SequentFormula<T> sequentFormula) {
        return insertAndRemoveRedundancyHelper(idx, sequentFormula,
                createSemisequentChangeInfo(seqList), null);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#replace(org.key_project.common.core.logic.calculus.PosInOccurrence, SeqFor)
     */
    @Override
    public CCSemisequentChangeInfo<T, SemiSeq> replace(
            PosInOccurrence<T> pos, SequentFormula<T> sequentFormula) {
        final int idx = indexOf(pos.sequentFormula());
        final FormulaChangeInfo<T> fci =
                new FormulaChangeInfo<T>(pos, sequentFormula);
        return insertAndRemoveRedundancyHelper(idx, sequentFormula,
                remove(idx), fci);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#replace(int, SeqFor)
     */
    @Override
    public CCSemisequentChangeInfo<T, SemiSeq> replace(
            int idx, SequentFormula<T> sequentFormula) {
        return insertAndRemoveRedundancyHelper(idx, sequentFormula,
                remove(idx), null);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#replace(org.key_project.common.core.logic.calculus.PosInOccurrence, org.key_project.util.collection.ImmutableList)
     */
    @Override
    public CCSemisequentChangeInfo<T, SemiSeq> replace(
            PosInOccurrence<T> pos, Iterable<SequentFormula<T>> replacements) {
        final int idx = indexOf(pos.sequentFormula());
        return insertAndRemoveRedundancy(idx, replacements, remove(idx));
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#replace(int, org.key_project.util.collection.ImmutableList)
     */
    @Override
    public CCSemisequentChangeInfo<T, SemiSeq> replace(
            int idx, Iterable<SequentFormula<T>> replacements) {
        return insertAndRemoveRedundancy(idx, replacements, remove(idx));
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#size()
     */
    @Override
    public int size() {
        return seqList.size();
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#remove(int)
     */
    @Override
    public CCSemisequentChangeInfo<T, SemiSeq> remove(int idx) {

        ImmutableList<SequentFormula<T>> newList = seqList;

        if (idx < 0 || idx >= size()) {
            return createSemisequentChangeInfo(seqList);
        }

        ImmutableList<SequentFormula<T>> temp = ImmutableSLList.<SequentFormula<T>>nil();
        for (int i = 0; i < idx; i++) {// go to idx
            temp = temp.prepend(newList.head());
            newList = newList.tail();
        }

        // remove the element that is at head of newList
        final SequentFormula<T> removedFormula = newList.head();
        newList = newList.tail();
        newList = newList.prepend((Iterable<SequentFormula<T>>) temp);

        // create change info object
        final CCSemisequentChangeInfo<T, SemiSeq> sci =
                createSemisequentChangeInfo(newList);
        sci.removedFormula(idx, removedFormula);

        return sci;
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#indexOf(SeqFor)
     */
    @Override
    public int indexOf(SequentFormula<T> sequentFormula) {
        ImmutableList<SequentFormula<T>> searchList = seqList;
        int index = 0;
        while (!searchList.isEmpty()) {
            if (searchList.head() == sequentFormula) {
                return index;
            }
            searchList = searchList.tail();
            index++;
        }
        return -1;
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#get(int)
     */
    @Override
    public SequentFormula<T> get(int idx) {
        if (idx < 0 || idx >= seqList.size()) {
            throw new IndexOutOfBoundsException();
        }
        return seqList.take(idx).head();
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#getFirst()
     */
    @Override
    public SequentFormula<T> getFirst() {
        return seqList.head();
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#contains(SeqFor)
     */
    @Override
    public boolean contains(SequentFormula<T> sequentFormula) {
        return indexOf(sequentFormula) != -1;
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#containsEqual(SeqFor)
     */
    @Override
    public boolean containsEqual(SequentFormula<T> sequentFormula) {
        return seqList.contains(sequentFormula);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#iterator()
     */
    @Override
    public Iterator<SequentFormula<T>> iterator() {
        return seqList.iterator();
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#asList()
     */
    @Override
    public ImmutableList<SequentFormula<T>> asList() {
        return seqList;
    }

    @SuppressWarnings("unchecked")
    public boolean equals(Object o) {
        if (!(o instanceof CCSemisequentImpl))
            return false;
        return seqList.equals(((CCSemisequentImpl<T, SemiSeq>) o).seqList);
    }

    public int hashCode() {
        return seqList.hashCode();
    }

    /** @return String representation of this Semisequent */
    public String toString() {
        return seqList.toString();
    }

}