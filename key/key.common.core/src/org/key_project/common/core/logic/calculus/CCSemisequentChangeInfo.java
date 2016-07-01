package org.key_project.common.core.logic.calculus;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public abstract class CCSemisequentChangeInfo<T extends CCTerm<?, ?, ?, T>, SemiSeq extends CCSemisequent<T, SemiSeq>> {

    /** contains the added formulas to the semisequent */
    private ImmutableList<SequentFormula<T>> added = ImmutableSLList.<SequentFormula<T>> nil();
    /** contains the removed formulas from the semisequent */
    private ImmutableList<SequentFormula<T>> removed = ImmutableSLList.<SequentFormula<T>> nil();
    /** contains the modified formulas from the semisequent */
    private ImmutableList<FormulaChangeInfo<T>> modified = ImmutableSLList
            .<FormulaChangeInfo<T>> nil();
    /** stores the redundance free formula list of the semisequent */
    protected ImmutableList<SequentFormula<T>> modifiedSemisequent = ImmutableSLList
            .<SequentFormula<T>> nil();
    /**
     * contains formulas that have been tried to add, but which have been
     * rejected due to already existing formulas in the sequent subsuming these
     * formulas
     */
    private ImmutableList<SequentFormula<T>> rejected = ImmutableSLList.<SequentFormula<T>> nil();
    /** */
    private int lastFormulaIndex = -1;

    protected CCSemisequentChangeInfo(ImmutableList<SequentFormula<T>> formulas) {
        this.modifiedSemisequent = formulas;
    }

    /**
     * returns true if the semisequent has changed
     */
    public boolean hasChanged() {
        return !added.isEmpty() ||
                !removed.isEmpty() ||
                !modified.isEmpty();
    }

    /**
     * sets the list of constrained formula containing all formulas of the
     * semisequent after the operation
     */
    public void setFormulaList(ImmutableList<SequentFormula<T>> list) {
        modifiedSemisequent = list;
    }

    /**
     * returns the list of constrained formula of the new semisequent
     */
    public ImmutableList<SequentFormula<T>> getFormulaList() {
        return modifiedSemisequent;
    }

    /**
     * logs an added formula at position idx
     */
    public void addedFormula(int idx, SequentFormula<T> cf) {
        added = added.prepend(cf);
        lastFormulaIndex = idx;
    }

    /**
     * logs a modified formula at position idx
     */
    public void modifiedFormula(int idx, FormulaChangeInfo<T> fci) {
        // This information can overwrite older records about removed
        // formulas
        removed = removed.removeAll
                (fci.getPositionOfModification().sequentFormula());
        modified = modified.prepend(fci);
        lastFormulaIndex = idx;
    }

    /**
     * returns the list of all added constrained formulas
     * 
     * @return IList<SeqFor> added to the semisequent
     */
    public ImmutableList<SequentFormula<T>> addedFormulas() {
        return added;
    }

    /**
     * returns the list of all removed constrained formulas
     * 
     * @return IList<SeqFor> removed from the semisequent
     */
    public ImmutableList<SequentFormula<T>> removedFormulas() {
        return removed;
    }

    /**
     * returns a list of formulas that have been tried to add to the semisequent
     * but got rejected as they were redundant
     * 
     * @return list of formulas rejected due to redundancy
     */
    public ImmutableList<SequentFormula<T>> rejectedFormulas() {
        return this.rejected;
    }

    /**
     * adding formula <tt>f</tt> to the semisequent failed due to a redundance
     * check. This means an equal or stronger formula is already present in the
     * semisequent
     * 
     * @param f
     *            the SeqFor
     */
    public void rejectedFormula(SequentFormula<T> f) {
        this.rejected = this.rejected.append(f);
    }

    /**
     * returns the list of all modification positions
     * 
     * @return IList<SeqFor> modified within the semisequent
     */
    public ImmutableList<FormulaChangeInfo<T>> modifiedFormulas() {
        return modified;
    }

    /**
     * logs an added formula at position idx
     */
    public void removedFormula(int idx, SequentFormula<T> cf) {
        removed = removed.prepend(cf);

        lastFormulaIndex =
                (lastFormulaIndex == idx) ? -1 :
                        lastFormulaIndex > idx ? lastFormulaIndex - 1
                                : lastFormulaIndex;

        if (lastFormulaIndex < -1) {
            lastFormulaIndex = -1;
        }

    }

    /**
     * This method combines this change information from this info and its
     * successor. ATTENTION: it takes over ownership over {@link succ} and does
     * not release it. This means when invoking the method it must be snsured
     * that succ is never used afterwards.
     */
    public void combine(CCSemisequentChangeInfo<T, ?> succ) {
        final CCSemisequentChangeInfo<T, SemiSeq> predecessor = this;
        if (succ == predecessor) {
            return;
        }

        for (SequentFormula<T> sf : succ.removed) {
            predecessor.added = predecessor.added.removeAll(sf);

            boolean skip = false;
            for (FormulaChangeInfo<T> fci : predecessor.modified) {
                if (fci.getNewFormula() == sf) {
                    predecessor.modified = predecessor.modified.removeAll(fci);
                    if (!predecessor.removed.contains(fci.getOriginalFormula())) {
                        predecessor.removed =
                                predecessor.removed.append(fci
                                        .getOriginalFormula());
                    }
                    skip = true;
                    break;
                }
            }
            if (!skip) {
                predecessor.removedFormula(succ.lastFormulaIndex, sf);
            }
        }

        for (FormulaChangeInfo<T> fci : succ.modified) {
            if (predecessor.addedFormulas().contains(fci.getOriginalFormula())) {
                predecessor.added =
                        predecessor.added.removeAll(fci.getOriginalFormula());
                predecessor.addedFormula(succ.lastFormulaIndex,
                        fci.getNewFormula());
            }
            else {
                predecessor.modifiedFormula(succ.lastFormulaIndex, fci);
            }
        }

        for (SequentFormula<T> sf : succ.added) {
            predecessor.removed = predecessor.removed.removeAll(sf);
            if (!predecessor.added.contains(sf)) {
                predecessor.addedFormula(succ.lastFormulaIndex, sf);
            }
        }

        for (SequentFormula<T> sf : succ.rejected) {
            if (!predecessor.rejected.contains(sf)) {
                predecessor.rejectedFormula(sf);
            }
        }

        predecessor.lastFormulaIndex = succ.lastFormulaIndex;
        predecessor.modifiedSemisequent = succ.modifiedSemisequent;
    }

    /**
     * returns the index of the last added formula
     */
    public int getIndex() {
        return lastFormulaIndex;
    }

    /**
     * creates a new semisequent containing the modified formulas
     * 
     * @param modifiedFormulas
     * @return
     */
    protected abstract SemiSeq createSemisequent(
            ImmutableList<SequentFormula<T>> modifiedFormulas);

    /**
     * returns the semisequent that is the result of the change operation
     */
    public SemiSeq semisequent() {
        return createSemisequent(modifiedSemisequent);
    }

    /**
     * toString
     */
    public String toString() {
        return "changed:" + hasChanged() +
                "\n  added (pos):" + added + "(" + lastFormulaIndex + ")" +
                "\n  removed:" + removed +
                "\n  modified:" + modified +
                "\n  rejected:" + rejected +
                "\n  new semisequent:" + modifiedSemisequent;
    }

}