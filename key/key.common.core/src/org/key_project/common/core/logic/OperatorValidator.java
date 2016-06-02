package org.key_project.common.core.logic;

import org.key_project.util.collection.ImmutableArray;

public interface OperatorValidator<S extends DLSort, T extends DLTerm<S, ? extends DLVisitor<T>>> {

    

    /**
     * Determines the sort of the {@link Term} if it would be created using this
     * Operator as top level operator and the given terms as sub terms. The
     * assumption that the constructed term would be allowed is not checked.
     * @param terms an array of Term containing the subterms of a (potential)
     * term with this operator as top level operator
     * @return sort of the term with this operator as top level operator of the
     * given substerms
     */
    S sort(ImmutableArray<T> terms);
    

    /**
     * Checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the {@link Term} is valid.
     */
    boolean validTopLevel(T term);
    
}
