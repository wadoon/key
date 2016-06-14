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

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.key_project.common.core.logic.GenericTerm;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public abstract class GenericSequent<SeqFor extends SequentFormula<?>, 
                                     SemiSeq extends GenericSemisequent<?, SeqFor>,
                                     Seq extends GenericSequent<SeqFor, SemiSeq, Seq>> implements Iterable<SeqFor> {

    public static final GenericSequent<?, ?, ?> EMPTY_SEQUENT = new NILSequent<>();

  

    private final GenericSemisequent<?, SeqFor> antecedent;

    private final GenericSemisequent<?, SeqFor> succedent;

    /**
     * must only be called by NILSequent
     *
     */
    private GenericSequent() {
        antecedent = GenericSemisequent.<T, SeqFor, GenericSemisequent<T, SeqFor>>nil();
        succedent  = GenericSemisequent.<T, SeqFor, GenericSemisequent<T, SeqFor>>nil();
    }
    
    /** creates new GenericSequent<T, SeqFor> with antecedence and succedence */
    private GenericSequent(GenericSemisequent<T, SeqFor> antecedent, GenericSemisequent<T, SeqFor> succedent) {
        assert !antecedent.isEmpty() || !succedent.isEmpty();
        this.antecedent = antecedent;
        this.succedent  = succedent;    
    }
    
    protected abstract AbstractSequentFactory<?,?> getSequentFactory();

    /** 
     * adds a formula to the antecedent (or succedent) of the
     * sequent. Depending on the value of first the formulas are
     * inserted at the beginning or end of the ante-/succedent.
     *  (NOTICE:GenericSequent<T, SeqFor> determines 
     * index using identy (==) not equality.)
     * @param cf the SeqFor to be added
     * @param antec boolean selecting the correct semisequent where to
     * insert the formulas. If set to true, the antecedent is taken
     * otherwise the succedent.
     * @param first boolean if true the formula is added at the
     * beginning of the ante-/succedent, otherwise to the end
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed 
     */
    public SequentChangeInfo addFormula(SeqFor cf, 
                    boolean antec, boolean first) {

    final GenericSemisequent<T, SeqFor> seq = antec ? antecedent : succedent;
    
    final GenericSemisequentChangeInfo<T, SeqFor, GenericSemisequent<T, SeqFor>> semiCI = first ? 
        seq.insertFirst(cf) : seq.insertLast(cf);   

    return SequentChangeInfo.createSequentChangeInfo
        (antec, semiCI, composeSequent(antec, semiCI.semisequent()), this); 
    }

    /** 
     * adds a formula to the sequent at the given
     * position. (NOTICE:GenericSequent<T, SeqFor> determines 
     * index using identy (==) not equality.)
     * @param cf a SeqFor to be added
     * @param p a PosInOccurrence<T, SeqFor> describes position in the sequent 
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed 
     */
    public SequentChangeInfo addFormula(SeqFor cf, 
            PosInOccurrence<T, SeqFor> p) {
    final GenericSemisequent<T, SeqFor> seq = getSemisequent(p);

    final GenericSemisequentChangeInfo<T, SeqFor, GenericSemisequent<T, SeqFor>> semiCI = seq.insert(seq.indexOf(p.sequentFormula()),cf);
    
    return SequentChangeInfo.createSequentChangeInfo
        (p.isInAntec(), semiCI, composeSequent(p.isInAntec(), semiCI.semisequent()), this);
    }

    /** 
     * adds list of formulas to the antecedent (or succedent) of the
     * sequent. Depending on the value of first the formulas are
     * inserted at the beginning or end of the ante-/succedent.
     *  (NOTICE:GenericSequent<T, SeqFor> determines 
     * index using identity (==) not equality.)
     * @param insertions the IList<SeqFor> to be added
     * @param antec boolean selecting the correct semisequent where to
     * insert the formulas. If set to true, the antecedent is taken
     * otherwise the succedent.
     * @param first boolean if true the formulas are added at the
     * beginning of the ante-/succedent, otherwise to the end
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed 
     */
    public SequentChangeInfo addFormula(ImmutableList<SeqFor> insertions,
                    boolean antec, boolean first) {

        final GenericSemisequent<T, SeqFor> seq = antec ? antecedent : succedent;

        final GenericSemisequentChangeInfo<T, SeqFor, GenericSemisequent<T, SeqFor>> semiCI = first ? seq.insertFirst(insertions) : seq.insertLast(insertions);

        return SequentChangeInfo.createSequentChangeInfo
                (antec, semiCI, composeSequent(antec, semiCI.semisequent()), this);
    }

    /** adds the formulas of list insertions to the sequent starting at
     * position p. (NOTICE:GenericSequent<T, SeqFor> determines 
     * index using identy (==) not equality.)
     * @param insertions a IList<SeqFor> with the formulas to be added
     * @param p the PosInOccurrence<T, SeqFor> describing the position where to
     * insert the formulas 
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed 
     */
    public SequentChangeInfo addFormula(ImmutableList<SeqFor> insertions, 
                    PosInOccurrence<T, SeqFor> p) {
    final GenericSemisequent<T, SeqFor> seq = getSemisequent(p);

    final GenericSemisequentChangeInfo<T, SeqFor, GenericSemisequent<T, SeqFor>> semiCI = 
        seq.insert(seq.indexOf(p.sequentFormula()), insertions);

    return SequentChangeInfo.createSequentChangeInfo
        (p.isInAntec(), semiCI, composeSequent(p.isInAntec(), semiCI.semisequent()), this);
    }

    /** returns semisequent of the antecedent to work with */
    public GenericSemisequent<T, SeqFor> antecedent() {
    return antecedent;
    }

    /** 
     * replaces the formula at the given position with another one
     * (NOTICE:GenericSequent<T, SeqFor> determines 
     * index using identity (==) not equality.)  
     * @param newCF the SeqFor replacing the old one
     * @param p a PosInOccurrence<T, SeqFor> describes position in the sequent 
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed 
     */
    public SequentChangeInfo changeFormula(SeqFor newCF,
                       PosInOccurrence<T, SeqFor> p) {     
    final GenericSemisequentChangeInfo<T, SeqFor, GenericSemisequent<T, SeqFor>> semiCI = 
            getSemisequent(p).replace(p, newCF);

    return SequentChangeInfo.createSequentChangeInfo
        (p.isInAntec(), semiCI, composeSequent(p.isInAntec(), semiCI.semisequent()), this);
    }

    /** 
     * replaces the formula at position p with the head of the given
     * list and adds the remaining list elements to the sequent
     * (NOTICE:GenericSequent<T, SeqFor> determines 
     * index using identity (==) not equality.)  
     * @param replacements the IList<SeqFor> whose head
     * replaces the formula at position p and adds the rest of the list
     * behind the changed formula
     * @param p a PosInOccurrence<T, SeqFor> describing the position of the formula
     * to be replaced
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed 
     */
    public SequentChangeInfo changeFormula(ImmutableList<SeqFor> replacements,
                       PosInOccurrence<T, SeqFor> p) {

    final GenericSemisequentChangeInfo<T, SeqFor, GenericSemisequent<T, SeqFor>> semiCI = 
            getSemisequent(p).replace(p, replacements);

    final SequentChangeInfo sci = 
            SequentChangeInfo.createSequentChangeInfo
            (p.isInAntec(), semiCI, composeSequent(p.isInAntec(), semiCI.semisequent()), this);

    return sci;
    }

    /** 
     * replaces the antecedent ({@code antec} is true) of this sequent by the given {@link GenericSemisequent<T, SeqFor>} 
     * similar for the succedent if {@code antec} is false.
     * @param antec if the antecedent or succedent shall be replaced 
     * @param semiSeq the {@link GenericSemisequent<T, SeqFor>} to use
     * @return the resulting sequent 
     */
    private GenericSequent<T, SeqFor> composeSequent(boolean antec, GenericSemisequent<T, SeqFor> semiSeq) {
        if (semiSeq.isEmpty()) {
            if (!antec && antecedent.isEmpty()) {
                return EMPTY_SEQUENT;
            } else if (antec && succedent.isEmpty()){
                return EMPTY_SEQUENT;
            }
        }

        if ((antec && semiSeq == antecedent) || (!antec && semiSeq == succedent)) {  
            return this;
        }   

        return new GenericSequent<T, SeqFor>(antec ? semiSeq : antecedent, antec ? succedent : semiSeq);
    }

    /**
     * determines if the sequent is empty.
     * @return true iff the sequent consists of two instances of
     * GenericSemisequent<T, SeqFor>.EMPTY_SEMISEQUENT
     */
    public boolean isEmpty() {
        return antecedent.isEmpty() && succedent.isEmpty();
    }


    public boolean equals(Object o) {
    if ( ! ( o instanceof GenericSequent<?, ?> ) ) 
        return false;
    @SuppressWarnings("unchecked")
    final GenericSequent<T, SeqFor> o1 = (GenericSequent<T, SeqFor>) o;
    return antecedent.equals(o1.antecedent)
        && succedent.equals(o1.succedent);
    }

    public int formulaNumberInSequent(boolean inAntec,
                                      SeqFor cfma) {
        int n = inAntec ? 0 : antecedent.size();
        final Iterator<SeqFor> formIter =
            inAntec ? antecedent.iterator() : succedent.iterator();
        while (formIter.hasNext()) {
            n++;
            if (formIter.next().equals(cfma)) return n;
        }
        throw new RuntimeException("Ghost formula "+cfma+" in sequent "+
                this+" [antec="+inAntec+"]");
    }

    public SeqFor getFormulabyNr(int formulaNumber) {
        if (formulaNumber <= 0 || formulaNumber>size()) {
            throw new RuntimeException("No formula nr. "+
                    formulaNumber+" in seq. "+this);
        }
        if (formulaNumber<=antecedent.size()) {
            return antecedent.get(formulaNumber - 1);
        }
        return succedent.get((formulaNumber-1)-antecedent.size());
    }

    /** returns the semisequent in which the SeqFor described
     * by PosInOccurrence<T, SeqFor> p lies
     */
    private GenericSemisequent<T, SeqFor> getSemisequent(PosInOccurrence<T, SeqFor> p) {
    return p.isInAntec() ? antecedent() : succedent();
    }

    public int hashCode () {
        return antecedent.hashCode () * 17 + succedent.hashCode ();
    }


    /** returns iterator about all ConstrainedFormulae of the sequent
     * @return iterator about all ConstrainedFormulae of the sequent
     */
    public Iterator<SeqFor> iterator() {
    return new SequentIterator<T, SeqFor>( antecedent(), succedent() );
    }


    public boolean numberInAntec(int formulaNumber) {
       return formulaNumber <= antecedent.size();
    }


    /** removes the formula at position p (NOTICE:GenericSequent<T, SeqFor> determines
     * index using identity (==) not equality.)
     * @param p a PosInOccurrence<T, SeqFor> that describes position in the sequent
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed
     */
    public SequentChangeInfo removeFormula(PosInOccurrence<T, SeqFor> p) {
    final GenericSemisequent<T, SeqFor> seq = getSemisequent(p);

    final GenericSemisequentChangeInfo<T, SeqFor, ?> semiCI = seq.remove(seq.indexOf(p.sequentFormula()));

    final SequentChangeInfo sci = createSequentChangeInfo
        (p.isInAntec(), semiCI, composeSequent(p.isInAntec(), semiCI.semisequent()), this);

    return sci;
    }

    /**
     * TODO: Document.
     *
     * @param inAntec
     * @param semiCI
     * @param composeSequent
     * @param genericSequent
     * @return
     */
    protected abstract SequentChangeInfo createSequentChangeInfo(boolean inAntec,
            GenericSemisequentChangeInfo<T, SeqFor, ?> semiCI,
            GenericSequent<T, SeqFor> composeSequent,
            GenericSequent<T, SeqFor> genericSequent);
    
    public int size () {
        return antecedent ().size () + succedent ().size ();
    }

    /** returns semisequent of the succedent to work with */
    public GenericSemisequent<T, SeqFor> succedent() {
    return succedent;
    }

    /** String representation of the sequent
     * @return String representation of the sequent */
    public String toString() {
    return antecedent().toString()+"==>"+succedent().toString();
    }

    /**
     * returns true iff the given variable is bound in a formula of a
     * SeqFor in this sequent.
     * @param v the bound variable to search for
     */
    public boolean varIsBound(QuantifiableVariable v) {
    final Iterator<SeqFor> it = iterator(); 
    while (it.hasNext()) {
        final BoundVarsVisitor bvv=new BoundVarsVisitor();
        it.next().formula().execPostOrder(bvv);
        if (bvv.getBoundVariables().contains(v)) {
        return true;
        }
    }
    return false;
    }

    static class NILSequent<T extends GenericTerm<?,?,?,T>, SeqFor extends SequentFormula<T>> extends GenericSequent<T, SeqFor> {
               
        public boolean isEmpty() {
            return true;
        }
                
        public Iterator<SeqFor> iterator() {
            return ImmutableSLList.<SeqFor>nil().iterator();
        }
        
        public boolean varIsBound(QuantifiableVariable v) {
            return false;
        }
        
    } 
    
    static class SequentIterator<T extends GenericTerm<?,?,?,T>, SeqFor extends SequentFormula<T>> implements Iterator<SeqFor> {

    private final Iterator<SeqFor> anteIt;
    private final Iterator<SeqFor> succIt;      

    SequentIterator(GenericSemisequent<T, SeqFor> ante, 
            GenericSemisequent<T, SeqFor> succ) {
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
    private static<T extends GenericTerm<?,?,?,T>> Set<Name> getLabelsForTermRecursively(T term) {
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
    public Set<Name> getOccuringTermLabels() {
        final Set<Name> result = new HashSet<Name>();
        for (final SeqFor sf : this) {
            result.addAll(getLabelsForTermRecursively(sf.formula()));
        }
        return result;
    }
}
