package org.key_project.common.core.logic.calculus;

import java.util.ArrayList;
import java.util.Iterator;

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
public abstract class CCSemisequentImpl<SeqFor extends SequentFormula<?>, SemiSeq extends CCSemisequent<SeqFor, SemiSeq>> implements CCSemisequent<SeqFor, SemiSeq> {

    /** list with the {@link SeqFor}s of the Semisequent */
    protected final ImmutableList<SeqFor> seqList;

    protected abstract CCSemisequentChangeInfo<SeqFor, SemiSeq> createSemisequentChangeInfo(
            ImmutableList<SeqFor> formulas);

    /** used by inner class Empty */
    protected CCSemisequentImpl() {
        seqList = ImmutableSLList.<SeqFor> nil();
    }

    /**
     * creates a new Semisequent with the Semisequent elements in seqList; the
     * provided list must be redundance free, i.e., the created sequent must be
     * exactly the same as when creating the sequent by subsequently inserting
     * all formulas
     */
    protected CCSemisequentImpl(ImmutableList<SeqFor> seqList) {
        assert !seqList.isEmpty();
        this.seqList = seqList;
    }

    /**
     * creates a new Semisequent with the Semisequent elements in seqList
     */
    public CCSemisequentImpl(SeqFor seqFormula) {
        assert seqFormula != null;
        this.seqList = ImmutableSLList.<SeqFor> nil().append(seqFormula);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#insert(int, SeqFor)
     */
    @Override
    public CCSemisequentChangeInfo<SeqFor, SemiSeq> insert(
            int idx, SeqFor sequentFormula) {
        return removeRedundance(idx, sequentFormula);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#insert(int, org.key_project.util.collection.ImmutableList)
     */
    @Override
    public CCSemisequentChangeInfo<SeqFor, SemiSeq> insert(
            int idx, ImmutableList<SeqFor> insertionList) {
        return removeRedundance(idx, insertionList);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#insertFirst(SeqFor)
     */
    @Override
    public CCSemisequentChangeInfo<SeqFor, SemiSeq> insertFirst(
            SeqFor sequentFormula) {
        return insert(0, sequentFormula);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#insertFirst(org.key_project.util.collection.ImmutableList)
     */
    @Override
    public CCSemisequentChangeInfo<SeqFor, SemiSeq> insertFirst(
            ImmutableList<SeqFor> insertions) {
        return insert(0, insertions);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#insertLast(SeqFor)
     */
    @Override
    public CCSemisequentChangeInfo<SeqFor, SemiSeq> insertLast(
            SeqFor sequentFormula) {
        return insert(size(), sequentFormula);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#insertLast(org.key_project.util.collection.ImmutableList)
     */
    @Override
    public CCSemisequentChangeInfo<SeqFor, SemiSeq> insertLast(
            ImmutableList<SeqFor> insertions) {
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
     * inserts new SeqFor at index idx and removes duplicates, perform
     * simplifications etc.
     * 
     * @param fci
     *            null if the formula to be added is new, otherwise an object
     *            telling which formula is replaced with the new formula
     *            <code>sequentFormula</code>, and what are the differences
     *            between the two formulas
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    private CCSemisequentChangeInfo<SeqFor, SemiSeq> insertAndRemoveRedundancyHelper(
            int idx,
            SeqFor sequentFormula,
            CCSemisequentChangeInfo<SeqFor, SemiSeq> semiCI,
            FormulaChangeInfo<SeqFor> fci) {

        // Search for equivalent formulas and weakest constraint
        ImmutableList<SeqFor> searchList = semiCI.getFormulaList();
        ImmutableList<SeqFor> newSeqList = ImmutableSLList.<SeqFor> nil();
        SeqFor cf;
        int pos = -1;

        while (!searchList.isEmpty()) {
            ++pos;
            cf = searchList.head();
            searchList = searchList.tail();

            // FIXME (DS):
            // the lines below compile if we set the generic type argument of
            // GenericSemisequent to "<T extends GenericTerm<?, ?, ?, T>, SeqFor
            // extends SequentFormula<T>".
            if (sequentFormula != null
                    && cf.formula().equalsModRenaming(sequentFormula.formula())) {

                semiCI.rejectedFormula(sequentFormula);
                return semiCI; // semisequent already contains formula

            }
            newSeqList = newSeqList.prepend(cf);
        }

        // compose resulting formula list
        if (fci == null)
            semiCI.addedFormula(idx, sequentFormula);
        else
            semiCI.modifiedFormula(idx, fci);

        if (idx > pos) {
            searchList = searchList.prepend(sequentFormula);
        }

        while (!newSeqList.isEmpty()) {
            searchList = searchList.prepend(newSeqList.head());
            newSeqList = newSeqList.tail();
            if (idx == pos) {
                searchList = searchList.prepend(sequentFormula);
            }
            --pos;
        }

        // add new formula list to result object
        semiCI.setFormulaList(searchList);

        return semiCI;
    }

    /**
     * . inserts new ConstrainedFormulas starting at index idx and removes
     * duplicates, perform simplifications etc.
     * 
     * @param sequentFormulasToBeInserted
     *            the {@link ImmutableList<SeqFor>} to be inserted at position
     *            idx
     * @param idx
     *            an int that means insert sequentFormula at the idx-th position
     *            in the semisequent
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    private CCSemisequentChangeInfo<SeqFor, SemiSeq> insertAndRemoveRedundancy(
            int idx,
            ImmutableList<SeqFor> sequentFormulasToBeInserted,
            CCSemisequentChangeInfo<SeqFor, SemiSeq> sci) {

        int pos = idx;
        ImmutableList<SeqFor> oldFormulas = sci.getFormulaList();

        while (!sequentFormulasToBeInserted.isEmpty()) {
            final SeqFor aSequentFormula = sequentFormulasToBeInserted.head();
            sequentFormulasToBeInserted = sequentFormulasToBeInserted.tail();

            sci =
                    insertAndRemoveRedundancyHelper(pos, aSequentFormula, sci,
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
    private CCSemisequentChangeInfo<SeqFor, SemiSeq> removeRedundance(
            int idx, ImmutableList<SeqFor> sequentFormula) {
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
    private CCSemisequentChangeInfo<SeqFor, SemiSeq> removeRedundance(
            int idx, SeqFor sequentFormula) {
        return insertAndRemoveRedundancyHelper(idx, sequentFormula,
                createSemisequentChangeInfo(seqList), null);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#replace(org.key_project.common.core.logic.calculus.PosInOccurrence, SeqFor)
     */
    @Override
    public CCSemisequentChangeInfo<SeqFor, SemiSeq> replace(
            PosInOccurrence<?, SeqFor> pos, SeqFor sequentFormula) {
        final int idx = indexOf(pos.sequentFormula());
        final FormulaChangeInfo<SeqFor> fci =
                new FormulaChangeInfo<SeqFor>(pos, sequentFormula);
        return insertAndRemoveRedundancyHelper(idx, sequentFormula,
                remove(idx), fci);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#replace(int, SeqFor)
     */
    @Override
    public CCSemisequentChangeInfo<SeqFor, SemiSeq> replace(
            int idx, SeqFor sequentFormula) {
        return insertAndRemoveRedundancyHelper(idx, sequentFormula,
                remove(idx), null);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#replace(org.key_project.common.core.logic.calculus.PosInOccurrence, org.key_project.util.collection.ImmutableList)
     */
    @Override
    public CCSemisequentChangeInfo<SeqFor, SemiSeq> replace(
            PosInOccurrence<?, SeqFor> pos, ImmutableList<SeqFor> replacements) {
        final int idx = indexOf(pos.sequentFormula());
        return insertAndRemoveRedundancy(idx, replacements, remove(idx));
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#replace(int, org.key_project.util.collection.ImmutableList)
     */
    @Override
    public CCSemisequentChangeInfo<SeqFor, SemiSeq> replace(
            int idx, ImmutableList<SeqFor> replacements) {
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
    public CCSemisequentChangeInfo<SeqFor, SemiSeq> remove(int idx) {

        ImmutableList<SeqFor> newList = seqList;
        ImmutableList<SeqFor> queue = ImmutableSLList.<SeqFor> nil();

        if (idx < 0 || idx >= size()) {
            return createSemisequentChangeInfo(seqList);
        }

        final ArrayList<SeqFor> temp = new ArrayList<>();

        for (int i = 0; i < idx; i++) {// go to idx
            temp.add(newList.head());
            newList = newList.tail();
        }

        for (int k = temp.size() - 1; k >= 0; k--)
            queue = queue.prepend(temp.get(k));

        // remove the element that is at head of newList
        final SeqFor removedFormula = newList.head();
        newList = newList.tail();
        newList = newList.prepend(queue);

        // create change info object
        final CCSemisequentChangeInfo<SeqFor, SemiSeq> sci =
                createSemisequentChangeInfo(newList);
        sci.removedFormula(idx, removedFormula);

        return sci;
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#indexOf(SeqFor)
     */
    @Override
    public int indexOf(SeqFor sequentFormula) {
        ImmutableList<SeqFor> searchList = seqList;
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
    public SeqFor get(int idx) {
        if (idx < 0 || idx >= seqList.size()) {
            throw new IndexOutOfBoundsException();
        }
        return seqList.take(idx).head();
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#getFirst()
     */
    @Override
    public SeqFor getFirst() {
        return seqList.head();
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#contains(SeqFor)
     */
    @Override
    public boolean contains(SeqFor sequentFormula) {
        return indexOf(sequentFormula) != -1;
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#containsEqual(SeqFor)
     */
    @Override
    public boolean containsEqual(SeqFor sequentFormula) {
        return seqList.contains(sequentFormula);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#iterator()
     */
    @Override
    public Iterator<SeqFor> iterator() {
        return seqList.iterator();
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSemisequent#asList()
     */
    @Override
    public ImmutableList<SeqFor> asList() {
        return seqList;
    }

    @SuppressWarnings("unchecked")
    public boolean equals(Object o) {
        if (!(o instanceof CCSemisequentImpl))
            return false;
        return seqList.equals(((CCSemisequentImpl<SeqFor, SemiSeq>) o).seqList);
    }

    public int hashCode() {
        return seqList.hashCode();
    }

    /** @return String representation of this Semisequent */
    public String toString() {
        return seqList.toString();
    }

}