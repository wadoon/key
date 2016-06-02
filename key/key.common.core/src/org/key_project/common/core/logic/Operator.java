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

package org.key_project.common.core.logic;

import org.key_project.common.core.logic.op.SVSubstitute;


/** 
 * All symbols acting as members of a term e.g. logical operators, predicates, 
 * functions, variables etc. have to implement this interface.  
 */
public interface Operator extends Named, SVSubstitute {
    
    /**
     * the arity of this operator  
     */
    int arity();
    

    
    /**
     * Tells whether the operator binds variables at the n-th subterm.
     */
    boolean bindVarsAt(int n);
    
    
    /**
     * Tells whether the operator is rigid.
     */
    boolean isRigid();      
    

}