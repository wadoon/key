package org.key_project.common.core.logic.calculus;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.sort.Sort;

/** 
 * A sequent formula is a wrapper around a formula that occurs 
 * as top level formula in a sequent. SequentFormula<JavaDLTerm> instances have
 * to be unique in the sequent as they are used by PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> 
 * to determine the exact position. In earlier KeY versions this class 
 * was called ConstrainedFormula as it was equipped with an additional 
 * constraints. It would be interesting to add more value to this class 
 * by providing a way to add additional annotations or to cache local information 
 * about the formula.
 */
public class SequentFormula<T extends CCTerm<?, ?, ?, T>> {

    protected final T term;
    protected final int hashCode;

    /** creates a new SequentFormula<JavaDLTerm> 
     * @param term of sort {@link Sort#FORMULA}
     */ 
    public SequentFormula(T term) {
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
    if (obj instanceof SequentFormula/*<S,N,V,T>*/) {
        SequentFormula<T> cmp=(SequentFormula<T>)obj;
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