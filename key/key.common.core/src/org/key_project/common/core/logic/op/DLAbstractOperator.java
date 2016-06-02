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

package org.key_project.common.core.logic.op;

import org.key_project.common.core.logic.DLOperator;
import org.key_project.common.core.logic.Name;
import org.key_project.util.collection.ImmutableArray;


/** 
 * Abstract operator class offering some common functionality.
 */
public abstract class DLAbstractOperator implements DLOperator {
    
    private final Name name;
    private final int arity;
    private final ImmutableArray<Boolean> whereToBind;
    private final boolean isRigid;
    
    
    protected DLAbstractOperator(Name name, 
	    		               int arity, 
	    		               ImmutableArray<Boolean> whereToBind,
	    		               boolean isRigid) {
	assert name != null;
	assert arity >= 0;
	assert whereToBind == null || whereToBind.size() == arity;	
	this.name = name;
	this.arity = arity;
	this.whereToBind = whereToBind;
	this.isRigid = isRigid;
    }
    
    
    protected DLAbstractOperator(Name name, 
	    		       int arity, 
	    		       Boolean[] whereToBind,
	    		       boolean isRigid) {
	this(name, arity, new ImmutableArray<Boolean>(whereToBind), isRigid);
    }        
    
    
    protected DLAbstractOperator(Name name, int arity, boolean isRigid) {
	this(name, arity, (ImmutableArray<Boolean>) null, isRigid);
    }
    
    
    protected final ImmutableArray<Boolean> whereToBind() {
	return whereToBind;
    }
    
    
    @Override
    public final Name name() {
	return name;
    }
    
    
    @Override
    public final int arity() {
        return arity;
    }
    
    
    @Override
    public final boolean bindVarsAt(int n) {
	return whereToBind != null && whereToBind.get(n);
    }
    
    
    @Override
    public final boolean isRigid() {
	return isRigid;
    }
    
    
   
    
    
    @Override
    public String toString() {
	return name().toString();
    }
}