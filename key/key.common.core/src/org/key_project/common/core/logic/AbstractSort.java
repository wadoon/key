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

import org.key_project.common.core.logic.op.SortDependingFunction;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * Abstract base class for implementations of the Sort interface.
 */
public abstract class AbstractSort implements Sort {
    
    private final Name name;
    protected final ImmutableSet<Sort> ext;    
    private final boolean isAbstract;

    
    public AbstractSort(Name name, ImmutableSet<Sort> ext, boolean isAbstract) {
    	this.name = name;
        this.ext = ext;
        this.isAbstract = isAbstract;
    }    
    
    @Override
    public final ImmutableSet<Sort> extendsSorts(TermServices<?,?> services) {
        return this == services.getFormulaSort() || this == services.getUpdateSort() || this == services.getAnySort()
                ? DefaultImmutableSet.<Sort>nil()
                : ext.isEmpty()
                  ? ext.add(services.getAnySort())
                  : ext;
    }

    
    @Override    
    public final boolean extendsTrans(Sort sort, TermServices<?,?> services) {
        if(sort == this) {
            return true;
        } else if(this == services.getFormulaSort() || this == services.getFormulaSort()) {
            return false;
        } else if(sort == services.getAnySort()) {
            return true;
        }
        for(Sort superSort : services.getDirectSuperSorts(sort)) {
            if(superSort == sort || superSort.extendsTrans(sort, services)) {
        	return true;
            }
        }
        
        return false;
    }
    

    @Override
    public final Name name() {
        return name;
    }
    
    
    @Override
    public final boolean isAbstract() {
	return isAbstract;
    }
    

    @Override
    public final SortDependingFunction getCastSymbol(TermServices<?,?> services) {
        SortDependingFunction result
            = SortDependingFunction.getFirstInstance(CAST_NAME, services)
        			   .getInstanceFor(this, services);
        assert result.getSortDependingOn() == this && result.sort() == this;
        return result;
    }
    
    
    @Override    
    public final SortDependingFunction getInstanceofSymbol(TermServices<?,?> services) {
	SortDependingFunction result
	    = SortDependingFunction.getFirstInstance(INSTANCE_NAME, services)
                                   .getInstanceFor(this, services);
	assert result.getSortDependingOn() == this; 
	return result;
    }    
    
    
    @Override
    public final SortDependingFunction getExactInstanceofSymbol(TermServices<?,?> services) {
	SortDependingFunction result
            = SortDependingFunction.getFirstInstance(EXACT_INSTANCE_NAME, services)
                                   .getInstanceFor(this, services);
	assert result.getSortDependingOn() == this;
	return result;
    }
    
    
    @Override
    public final String toString() {
        return name.toString();
    }

    public String declarationString() {
        return name.toString();
    }
}