// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Provides methods used in type checking.<br/>
 * 
 * <strong>TODO:</strong> This should be named something like
 * "TypeCheckingAndInferenceService" and not be used for assembling actual
 * terms.
 */
public interface Operator extends Named, SVSubstitute, GenericOperator {

    /**
     * Determines the sort of the {@link Term} if it would be created using this
     * Operator as top level operator and the given terms as sub terms. The
     * assumption that the constructed term would be allowed is not checked.
     * 
     * @param terms
     *            an array of Term containing the subterms of a (potential) term
     *            with this operator as top level operator
     * @return sort of the term with this operator as top level operator of the
     *         given substerms
     */
    Sort sort(ImmutableArray<Term> terms);

    /**
     * Checks whether the top level structure of the given @link Term is
     * syntactically valid, given the assumption that the top level operator of
     * the term is the same as this Operator. The assumption that the top level
     * operator and the term are equal is NOT checked.
     * 
     * @return true iff the top level structure of the {@link Term} is valid.
     */
    boolean validTopLevel(Term term);
}