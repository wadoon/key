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

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Named;

/**
 * Generic interface for an operator. All symbols acting as members of a term
 * e.g. logical operators, predicates, functions, variables etc. have to
 * implement this interface.<br/>
 * 
 * <strong>TODO:</strong> This should be named "Operator"; the previous
 * {@link Operator} interface should get the name
 * "TypeCheckingAndInferenceService" or the like.
 *
 * @author Dominic Scheurer
 */
public interface GenericOperator extends Named, SVSubstitute {

    /**
     * the arity of this operator
     */
    int arity();

    /**
     * Tells whether the operator binds variables at the n-th subterm.
     */
    boolean bindVarsAt(int n);
    
    /**
     * @return true iff this operator binds any variables
     */
    boolean bindsVars();

    /**
     * Tells whether the operator is rigid.
     */
    boolean isRigid();

}