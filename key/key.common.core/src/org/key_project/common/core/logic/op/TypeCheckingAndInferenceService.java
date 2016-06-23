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

package org.key_project.common.core.logic.op;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * A {@link TypeCheckingAndInferenceService} performs type checking and sort
 * inference by supplying methods previously defined by the {@link Operator}
 * class which, however, were not Operator-related.
 *
 * @author Dominic Scheurer
 *
 * @param <O>
 *            The concrete operator class for which to check and infer types.
 */
public interface TypeCheckingAndInferenceService<O extends Operator> {

    /**
     * Computes the sort of the given operator when instantiated with the given
     * sub terms.
     *
     * @param terms
     *            The sub terms for the operator.
     * @param op
     *            The operator.
     * @return The sort of the given operator when instantiated with the given
     *         sub terms.
     */
    Sort sort(ImmutableArray<? extends CCTerm<?, ?, ?>> terms, O op);

    /**
     * Checks whether the top level structure of the given @link GenericTerm is
     * syntactically valid, given the assumption that the top level operator of
     * the term is the same as this Operator. The assumption that the top level
     * operator and the term are equal is NOT checked.
     * 
     * @return true iff the top level structure of the {@link CCTerm} is valid.
     */
    boolean validTopLevel(CCTerm<?, ?, ?> term, O op);

}