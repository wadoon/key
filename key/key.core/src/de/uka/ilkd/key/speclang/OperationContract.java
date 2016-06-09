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

package de.uka.ilkd.key.speclang;

import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public interface OperationContract extends Contract {
    
    @Override
    public IProgramMethod getTarget();
    
    /**
     * Returns <code>true</code> iff the method (according to the contract) does
     * not modify the heap at all, i.e., iff it is "strictly pure."
     * 
     * @return whether this contract is strictly pure.
     */
    public boolean hasModifiesClause(LocationVariable heap);
    
    /**
     * Returns the modifies clause of the contract.
     */
    public JavaDLTerm getMod(LocationVariable heapVar, ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
                       Services services);
    
    
    /**
     * Returns the modifies clause of the contract.
     */
    public JavaDLTerm getMod(LocationVariable heapVar, JavaDLTerm heapTerm,
	               JavaDLTerm selfTerm, 
	    	       ImmutableList<JavaDLTerm> paramTerms,
                       Services services);

    public JavaDLTerm getFreePre(LocationVariable heap,
                           ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars,
                           Map<LocationVariable,? extends ProgramVariable> atPreVars,
                           Services services);

    public JavaDLTerm getFreePre(List<LocationVariable> heapContext,
                           ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars,
                           Map<LocationVariable,? extends ProgramVariable> atPreVars,
                           Services services);
    
    public JavaDLTerm getFreePre(LocationVariable heap,
                           JavaDLTerm heapTerm,
                           JavaDLTerm selfTerm,
                           ImmutableList<JavaDLTerm> paramTerms,
                           Map<LocationVariable,JavaDLTerm> atPres,
                           Services services);
}