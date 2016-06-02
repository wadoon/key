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

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Sort;
import org.key_project.common.core.logic.Sorted;
import org.key_project.common.core.logic.op.DLAbstractSortedOperator;
import org.key_project.common.core.logic.op.SortedOperator;
import org.key_project.util.collection.ImmutableArray;


/** 
 * Abstract sorted operator class offering some common functionality.
 */
public abstract class AbstractSortedOperator extends DLAbstractSortedOperator 
                                      implements SortedOperator, Sorted {

    protected AbstractSortedOperator(Name name,
	    			         ImmutableArray<Sort> argSorts,
	    		             org.key_project.common.core.logic.Sort sort,
	    		             ImmutableArray<Boolean> whereToBind,
	    		             boolean isRigid) {
        super(name, argSorts, sort, whereToBind, isRigid);
    }
    
    
    protected AbstractSortedOperator(Name name,
	    			        Sort[] argSorts,
	    		             org.key_project.common.core.logic.Sort sort,
	    		             Boolean[] whereToBind,
	    		             boolean isRigid) {
	this(name, 
             new ImmutableArray<Sort>(argSorts), 
             sort, 
             new ImmutableArray<Boolean>(whereToBind), 
             isRigid);
    }    
    
    
    protected AbstractSortedOperator(Name name,
	    			         ImmutableArray<Sort> argSorts,
	    		             org.key_project.common.core.logic.Sort sort,
	    		             boolean isRigid) {
	this(name, argSorts, sort, null, isRigid);
    }    
    
    
    protected AbstractSortedOperator(Name name,
	    			         Sort[] argSorts,
	    		             org.key_project.common.core.logic.Sort sort,
	    		             boolean isRigid) {
	this(name, new ImmutableArray<Sort>(argSorts), sort, null, isRigid);
    }
    
    
    protected AbstractSortedOperator(Name name,
	    		             org.key_project.common.core.logic.Sort sort,
	    		             boolean isRigid) {
	this(name, (ImmutableArray<Sort>) null, sort, null, isRigid);
    }    
    

  
}
