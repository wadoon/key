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

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.util.collection.ImmutableList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public abstract class CCSequentImpl<T extends CCTerm<?, ?, ?, T>, SeqFor extends SequentFormula<T>, SemiSeq extends CCSemisequent<SeqFor, SemiSeq>, Seq extends CCSequent<T, SeqFor, SemiSeq, Seq>>
                          implements CCSequent<T, SeqFor, SemiSeq, Seq> {

    private final SemiSeq antecedent;

    private final SemiSeq succedent;

    protected abstract AbstractSequentFactory<SemiSeq, Seq> getSequentFactory();

    /**
     * TODO: Document.
     *
     * @param inAntec
     * @param semiCI
     * @param composeSequent
     * @param genericSequent
     * @return
     */
    protected abstract CCSequentChangeInfo<T, SeqFor, SemiSeq, Seq> createSequentChangeInfo(
            boolean inAntec,
            CCSemisequentChangeInfo<SeqFor, SemiSeq> semiCI,
            Seq composeSequent,
            Seq genericSequent);

    /** creates new GenericSequent<T, SeqFor> with antecedence and succedence */
    protected CCSequentImpl(SemiSeq antecedent, SemiSeq succedent) {
        this.antecedent = antecedent;
        this.succedent = succedent;
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#addFormula(SeqFor, boolean, boolean)
     */
    @Override
    @SuppressWarnings("unchecked")
    public CCSequentChangeInfo<T, SeqFor, SemiSeq, Seq> addFormula(SeqFor cf,
                                                                        boolean antec, boolean first) {

        final CCSemisequent<SeqFor, SemiSeq> seq =
                antec ? antecedent : succedent;

        final CCSemisequentChangeInfo<SeqFor, SemiSeq> semiCI =
                first ? seq.insertFirst(cf) : seq.insertLast(cf);

        return createSequentChangeInfo(antec, semiCI,
                composeSequent(antec, semiCI.semisequent()), (Seq) this);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#addFormula(SeqFor, org.key_project.common.core.logic.calculus.PosInOccurrence)
     */
    @Override
    @SuppressWarnings("unchecked")
    public CCSequentChangeInfo<T, SeqFor, SemiSeq, Seq> addFormula(SeqFor cf, PosInOccurrence<T, SeqFor> p) {
        final CCSemisequent<SeqFor, SemiSeq> seq = getSemisequent(p);

        final CCSemisequentChangeInfo<SeqFor, SemiSeq> semiCI =
                seq.insert(seq.indexOf(p.sequentFormula()), cf);

        return createSequentChangeInfo(p.isInAntec(), semiCI,
                composeSequent(p.isInAntec(), semiCI.semisequent()), (Seq) this);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#addFormula(org.key_project.util.collection.ImmutableList, boolean, boolean)
     */
    @Override
    @SuppressWarnings("unchecked")
    public CCSequentChangeInfo<T, SeqFor, SemiSeq, Seq> addFormula(
            ImmutableList<SeqFor> insertions,
            boolean antec, boolean first) {

        final CCSemisequent<SeqFor, SemiSeq> seq =
                antec ? antecedent : succedent;

        final CCSemisequentChangeInfo<SeqFor, SemiSeq> semiCI =
                first ? seq.insertFirst(insertions) : seq
                        .insertLast(insertions);

        return createSequentChangeInfo(antec, semiCI,
                composeSequent(antec, semiCI.semisequent()), (Seq) this);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#addFormula(org.key_project.util.collection.ImmutableList, org.key_project.common.core.logic.calculus.PosInOccurrence)
     */
    @Override
    @SuppressWarnings("unchecked")
    public  CCSequentChangeInfo<T, SeqFor, SemiSeq, Seq> addFormula(
            ImmutableList<SeqFor> insertions,
            PosInOccurrence<?, SeqFor> p) {
        final CCSemisequent<SeqFor, SemiSeq> seq = getSemisequent(p);

        final CCSemisequentChangeInfo<SeqFor, SemiSeq> semiCI =
                seq.insert(seq.indexOf(p.sequentFormula()), insertions);

        return createSequentChangeInfo(p.isInAntec(), semiCI,
                composeSequent(p.isInAntec(), semiCI.semisequent()), (Seq) this);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#antecedent()
     */
    @Override
    public SemiSeq antecedent() {
        return antecedent;
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#changeFormula(SeqFor, org.key_project.common.core.logic.calculus.PosInOccurrence)
     */
    @Override
    @SuppressWarnings("unchecked")
    public CCSequentChangeInfo<T, SeqFor, SemiSeq, Seq> changeFormula(
            SeqFor newCF,
            PosInOccurrence<?, SeqFor> p) {
        final CCSemisequentChangeInfo<SeqFor, SemiSeq> semiCI =
                getSemisequent(p).replace(p, newCF);

        return createSequentChangeInfo(p.isInAntec(), semiCI,
                composeSequent(p.isInAntec(), semiCI.semisequent()), (Seq) this);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#changeFormula(org.key_project.util.collection.ImmutableList, org.key_project.common.core.logic.calculus.PosInOccurrence)
     */
    @Override
    public CCSequentChangeInfo<T, SeqFor, SemiSeq, Seq> changeFormula(
            ImmutableList<SeqFor> replacements,
            PosInOccurrence<?, SeqFor> p) {

        final CCSemisequentChangeInfo<SeqFor, SemiSeq> semiCI =
                getSemisequent(p).replace(p, replacements);

        @SuppressWarnings("unchecked")
        final CCSequentChangeInfo<T, SeqFor, SemiSeq, Seq> sci =
                createSequentChangeInfo(p.isInAntec(),
                        semiCI,
                        composeSequent(p.isInAntec(), semiCI.semisequent()),
                        (Seq) this);

        return sci;
    }

    /**
     * replaces the antecedent ({@code antec} is true) of this sequent by the
     * given {@link GenericSemisequent<SeqFor, SemiSeq>} similar for the
     * succedent if {@code antec} is false.
     * 
     * @param antec
     *            if the antecedent or succedent shall be replaced
     * @param semiSeq
     *            the {@link GenericSemisequent<SeqFor, SemiSeq>} to use
     * @return the resulting sequent
     */
    private Seq composeSequent(boolean antec,
            SemiSeq semiSeq) {
        if (semiSeq.isEmpty()) {
            if (!antec && antecedent.isEmpty()) {
                return getSequentFactory().nil();
            }
            else if (antec && succedent.isEmpty()) {
                return getSequentFactory().nil();
            }
        }

        if ((antec && semiSeq == antecedent)
                || (!antec && semiSeq == succedent)) {
            @SuppressWarnings("unchecked")
            final Seq result = (Seq) this;
            return result;
        }

        return getSequentFactory().createSequent(antec ? semiSeq
                : antecedent, antec ? succedent : semiSeq);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return antecedent.isEmpty() && succedent.isEmpty();
    }

    public boolean equals(Object o) {
        if (!(o instanceof CCSequentImpl<?, ?, ?, ?>))
            return false;
        final CCSequentImpl<?, ?, ?, ?> o1 = (CCSequentImpl<?, ?, ?, ?>) o;
        return antecedent.equals(o1.antecedent)
                && succedent.equals(o1.succedent);
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#formulaNumberInSequent(boolean, SeqFor)
     */
    @Override
    public int formulaNumberInSequent(boolean inAntec, SeqFor cfma) {
        int n = inAntec ? 0 : antecedent.size();
        final Iterator<SeqFor> formIter =
                inAntec ? antecedent.iterator() : succedent.iterator();
        while (formIter.hasNext()) {
            n++;
            if (formIter.next().equals(cfma))
                return n;
        }
        throw new RuntimeException("Ghost formula " + cfma + " in sequent "
                + this + " [antec=" + inAntec + "]");
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#getFormulabyNr(int)
     */
    @Override
    public SeqFor getFormulabyNr(int formulaNumber) {
        if (formulaNumber <= 0 || formulaNumber > size()) {
            throw new RuntimeException("No formula nr. " + formulaNumber
                    + " in seq. " + this);
        }
        if (formulaNumber <= antecedent.size()) {
            return antecedent.get(formulaNumber - 1);
        }
        return succedent.get((formulaNumber - 1) - antecedent.size());
    }

    /**
     * returns the semisequent in which the SeqFor described by
     * PosInOccurrence<?, SeqFor> p lies
     */
    protected SemiSeq getSemisequent(
            PosInOccurrence<?, SeqFor> p) {
        return p.isInAntec() ? antecedent() : succedent();
    }

    public int hashCode() {
        return antecedent.hashCode() * 17 + succedent.hashCode();
    }

    /**
     * returns iterator about all ConstrainedFormulae of the sequent
     * 
     * @return iterator about all ConstrainedFormulae of the sequent
     */
    public Iterator<SeqFor> iterator() {
        return new SequentIterator<SeqFor, SemiSeq, Seq>(antecedent(),
                succedent());
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#numberInAntec(int)
     */
    @Override
    public boolean numberInAntec(int formulaNumber) {
        return formulaNumber <= antecedent.size();
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#removeFormula(org.key_project.common.core.logic.calculus.PosInOccurrence)
     */
    @Override
    public CCSequentChangeInfo<T, SeqFor, SemiSeq, Seq> removeFormula(
            PosInOccurrence<?, SeqFor> p) {
        final CCSemisequent<SeqFor, SemiSeq> seq = getSemisequent(p);

        final CCSemisequentChangeInfo<SeqFor, SemiSeq> semiCI =
                seq.remove(seq.indexOf(p.sequentFormula()));

        @SuppressWarnings("unchecked")
        final CCSequentChangeInfo<T, SeqFor, SemiSeq, Seq> sci =
                createSequentChangeInfo(p.isInAntec(), semiCI,
                        composeSequent(p.isInAntec(), semiCI.semisequent()),
                        (Seq) this);

        return sci;
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#size()
     */
    @Override
    public int size() {
        return antecedent().size() + succedent().size();
    }

    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#succedent()
     */
    @Override
    public SemiSeq succedent() {
        return succedent;
    }

    /**
     * String representation of the sequent
     * 
     * @return String representation of the sequent
     */
    public String toString() {
        return antecedent().toString() + "==>" + succedent().toString();
    }

    static class SequentIterator<SeqFor extends SequentFormula<?>, SemiSeq extends CCSemisequent<SeqFor, SemiSeq>, Seq extends CCSequent<?, SeqFor, SemiSeq, Seq>>
            implements Iterator<SeqFor> {

        private final Iterator<SeqFor> anteIt;
        private final Iterator<SeqFor> succIt;

        SequentIterator(CCSemisequent<SeqFor, SemiSeq> ante,
                CCSemisequent<SeqFor, SemiSeq> succ) {
            this.anteIt = ante.iterator();
            this.succIt = succ.iterator();
        }

        public boolean hasNext() {
            return anteIt.hasNext() || succIt.hasNext();
        }

        public SeqFor next() {
            if (anteIt.hasNext()) {
                return anteIt.next();
            }
            return succIt.next();
        }

        /**
         * throw an unsupported operation exception as sequents are immutable
         */
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    /*
     * Returns names of TermLabels, that occur in term or one of its subterms.
     */
    private Set<Name> getLabelsForTermRecursively(
            T term) {
        Set<Name> result = new HashSet<Name>();

        if (term.hasLabels()) {
            for (TermLabel label : term.getLabels()) {
                result.add(label.name());
            }
        }

        for (final T subTerm : term.subs()) {
            result.addAll(getLabelsForTermRecursively(subTerm));
        }

        return result;
    }

    /*
     * Returns names of TermLabels, that occur in this sequent.
     */
    /* (non-Javadoc)
     * @see org.key_project.common.core.logic.calculus.CCSequent#getOccuringTermLabels()
     */
    @Override
    public Set<Name> getOccuringTermLabels() {
        final Set<Name> result = new HashSet<Name>();
        for (final SeqFor sf : this) {
            result.addAll(getLabelsForTermRecursively(sf.formula()));
        }
        return result;
    }
}
