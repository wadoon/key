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

import org.key_project.common.core.logic.DLOperator;
import org.key_project.common.core.logic.Named;
import org.key_project.common.core.logic.op.SVSubstitute;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;


/** 
 * All symbols acting as members of a term e.g. logical operators, predicates, 
 * functions, variables etc. have to implement this interface.  
 */
public interface Operator extends DLOperator<Term>, Named, SVSubstitute {
    

    /**
     * {@inheritDoc}
     */
    @Override
    Sort sort(ImmutableArray<Term> terms);
    
    
    
    /**
     * {@inheritDoc}
     */
    @Override
    boolean validTopLevel(Term term);
}