package de.uka.ilkd.key.logic.op;

import org.key_project.common.core.logic.Sort;
import org.key_project.common.core.logic.SpecialSorts;
import org.key_project.common.core.logic.TermServices;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;

public class JavaDLOperatorValidator {

    //AbstractSortedOperator
    
    /**
     * checks if a given Term could be subterm (at the at'th subterm
     * position) of a term with this function at its top level. The
     * validity of the given subterm is NOT checked.  
     * @param at theposition of the term where this method should check 
     * the validity.  
     * @param possibleSub the subterm to be ckecked.
     * @return true iff the given term can be subterm at the indicated
     * position
     */
    private boolean possibleSub(int at, Term possibleSub) {
    final org.key_project.common.core.logic.Sort s = possibleSub.sort();

    return s == AbstractTermTransformer.METASORT
           || s instanceof ProgramSVSort
           || argSort(at) == AbstractTermTransformer.METASORT
           || argSort(at) instanceof ProgramSVSort
           || s.extendsTrans(argSort(at));
    }
    
    
    /**
     * Allows subclasses to impose custom demands on what constitutes a 
     * valid term using the operator represented by the subclass. The
     * default implementation here does not impose any such demands.
     */    
    protected boolean additionalValidTopLevel2(Term term) {
    return true;
    }
    
    
    @Override
    protected final boolean additionalValidTopLevel(Term term) {
    for(int i = 0, n = arity(); i < n; i++) {
            if(!possibleSub(i, term.sub(i))) { 
        return false;
        }
    }
    return additionalValidTopLevel2(term);
    }

// IfExThenElse
    @Override
    public Sort sort(ImmutableArray<Term> terms) {
    return terms.get(1).sort();
    }
    

    @Override
    protected boolean additionalValidTopLevel(Term term) {
        for(QuantifiableVariable var : term.varsBoundHere(0)) {
            if(!var.sort().name().toString().equals("int")) {
            return false;
            }
        }

        final org.key_project.common.core.logic.Sort s0 = term.sub(0).sort();
        final Sort s1 = term.sub(1).sort();
        final Sort s2 = term.sub(2).sort();
        
        return s0 == SpecialSorts.FORMULA && s1.equals(s2);
    }
    
    
    // IfThenElse
    
    @Override
    public org.key_project.common.core.logic.Sort sort(ImmutableArray<Term> terms, TermServices services) {
        final org.key_project.common.core.logic.Sort s2 = terms.get(1).sort();
        final org.key_project.common.core.logic.Sort s3 = terms.get(2).sort();
        if(s2 instanceof ProgramSVSort
             || s2 == AbstractTermTransformer.METASORT ) { 
            return s3; 
        } else if(s3 instanceof ProgramSVSort
              || s3 == AbstractTermTransformer.METASORT ) {
            return s2;
        } else {           
            return getCommonSuperSort(s2, s3, services);
        }
    }
    

    /*@Override
    protected boolean additionalValidTopLevel(Term term) {
        final org.key_project.common.core.logic.Sort s0 = term.sub(0).sort();
        final org.key_project.common.core.logic.Sort s1 = term.sub(1).sort();
        final org.key_project.common.core.logic.Sort s2 = term.sub(2).sort();
        
        return s0 == SpecialSorts.FORMULA
               && (s1 == SpecialSorts.FORMULA) == (s2 == SpecialSorts.FORMULA)
               && s1 != SpecialSorts.UPDATE 
               && s2 != SpecialSorts.UPDATE;
    }*/

    //SubstOp
    /**
     * @return sort of the second subterm or throws an
     * IllegalArgumentException if the given term has no correct (2=) arity
     */
    @Override
    public Sort sort(ImmutableArray<Term> terms) {
    if(terms.size() == 2) {
        return terms.get(1).sort();
    }
    else throw new IllegalArgumentException("Cannot determine sort of "+
                        "invalid term (Wrong arity).");
    }
    

    /**
     * @return true iff the sort of the subterm 0 of the given term
     * has the same sort as or a subsort of the variable to be substituted 
     * and the
     * term's arity is 2 and the numer of variables bound there is 0
     * for the 0th subterm and 1 for the 1st subterm.
     */
    @Override    
    protected boolean additionalValidTopLevel(Term term){
    if(term.varsBoundHere(1).size() != 1) { 
        return false;
    }
    return term.sub(0).sort().extendsTrans(term.varsBoundHere(1).get(0).sort());
    }
    
    // Observer

    @Override
    public Sort sort(ImmutableArray<Term> terms, TermServices services) {
        return sort();
    }

    @Override
    public boolean validTopLevel(Term term) {
        return false;
    }
    
    // UpdateApp
    @Override    
    public Sort sort(ImmutableArray<Term> terms) {
    return terms.get(1).sort();
    }    
    
    
    @Override
    public boolean additionalValidTopLevel (Term term) {
        return term.sub(0).sort() == SpecialSorts.UPDATE;
    }
    
    
    //AbstractOperator

    @Override
    public boolean validTopLevel(Term term) {
        if(arity() != term.arity()
                || arity() != term.subs().size()
                || (whereToBind() == null) != term.boundVars().isEmpty()) {
            return false;
        }

        for(int i = 0, n = arity(); i < n; i++) {
            if(term.sub(i) == null) {
                return false;
            }
        }

        return additionalValidTopLevel(term);
    }
    
    // TermSV
    
    
    // NullSort
    @Override
    public ImmutableSet<Sort> extendsSorts() {
    throw new UnsupportedOperationException(
          "NullSort.extendsSorts() cannot be supported");
    }
    
}
