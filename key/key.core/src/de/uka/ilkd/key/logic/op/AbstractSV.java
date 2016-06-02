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
import org.key_project.util.collection.ImmutableArray;

/**
 * Abstract base class for schema variables.
 */
public abstract class AbstractSV extends AbstractSortedOperator 
                          implements SchemaVariable {   
    
    private final boolean isStrict;
    
    
    protected AbstractSV(Name name, 
	                 ImmutableArray<Sort> argSorts, 
	                 org.key_project.common.core.logic.Sort sort,
	                 boolean isRigid,
	                 boolean isStrict) {
	super(name, argSorts, sort, isRigid);
	this.isStrict = isStrict;
    }
    
    
    protected AbstractSV(Name name, 
	                 Sort[] argSorts, 
	                 org.key_project.common.core.logic.Sort sort,
	                 boolean isRigid,
	                 boolean isStrict) {
	this(name, new ImmutableArray<Sort>(argSorts), sort, isRigid, isStrict);
    }
    
    
    protected AbstractSV(Name name,  
	                 org.key_project.common.core.logic.Sort sort,
	                 boolean isRigid,
	                 boolean isStrict) {
	this(name,(ImmutableArray<Sort>) null, sort, isRigid, isStrict);
    }    
        
    
    protected final String toString(String sortSpec) {
	return name() +" (" + sortSpec + ")"; 
    }    

    
    @Override
    public final boolean isStrict() {
	return isStrict;
    }
}