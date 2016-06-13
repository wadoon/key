package org.key_project.common.core.logic.calculus;

import org.key_project.common.core.logic.GenericTerm;
import org.key_project.common.core.logic.Visitor;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.program.GenericNameAbstractionTable;


public class GenericSequentFormula<S, N extends GenericNameAbstractionTable<S>, V extends Visitor<S,N,V,T>, T extends GenericTerm<S,N,V,T>> {

    protected final T term;
    protected final int hashCode;

    public GenericSequentFormula(T term) {
        if (term.sort() != Sort.FORMULA) {
            throw new RuntimeException("A term instead of a formula: " + term);
        }
        this.term = term;   
        this.hashCode = term.hashCode () * 13;
    }

    /** @return the stored JavaDLTerm */
    public T formula() { 
        return term;
    }

    /** equal if terms and constraints are equal */
    @SuppressWarnings("unchecked")
    public boolean equals(Object obj) {
        if (this == obj) { return true; }
    if (obj instanceof GenericSequentFormula/*<S,N,V,T>*/) {
        GenericSequentFormula<S,N,V,T> cmp=(GenericSequentFormula<S,N,V,T>)obj;
        if (term.equals(cmp.formula())) {
    	return true;
        }
    }
    return false;
    }

    /** String representation */
    public String toString() {
    return term.toString();
    }

    public int hashCode() {
        return hashCode;
    }

}