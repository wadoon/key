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
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;


/**
 * A contract about an operation (i.e., a method or a constructor), consisting 
 * of a precondition, a postcondition, a modifies clause, a measured-by clause, 
 * and a modality.
 */
public interface FunctionalOperationContract extends OperationContract {

    /**
     * Returns the modality of the contract.
     */
    public Modality getModality();

    public boolean isReadOnlyContract(Services services);

    public JavaDLTerm getEnsures(LocationVariable heap);

    /**
     * Returns the postcondition of the contract.
     */
    public JavaDLTerm getPost(LocationVariable heap,
                        ProgramVariable selfVar, 
	    	        ImmutableList<ProgramVariable> paramVars, 
	    	        ProgramVariable resultVar, 
	    	        ProgramVariable excVar,
	    	        Map<LocationVariable,? extends ProgramVariable> atPreVars,
	    	        Services services);

    public JavaDLTerm getPost(List<LocationVariable> heapContext,
                        ProgramVariable selfVar, 
	    	        ImmutableList<ProgramVariable> paramVars, 
	    	        ProgramVariable resultVar, 
	    	        ProgramVariable excVar,
	    	        Map<LocationVariable,? extends ProgramVariable> atPreVars,
	    	        Services services);
    
    /**
     * Returns the postcondition of the contract.
     */
    public JavaDLTerm getPost(LocationVariable heap,
                        JavaDLTerm heapTerm,
                        JavaDLTerm selfTerm,
                        ImmutableList<JavaDLTerm> paramTerms,
                        JavaDLTerm resultTerm,
                        JavaDLTerm excTerm,
	    	        Map<LocationVariable,JavaDLTerm> atPres,
	    	        Services services);

    public JavaDLTerm getPost(List<LocationVariable> heapContext,
                        Map<LocationVariable,JavaDLTerm> heapTerms,
                        JavaDLTerm selfTerm,
                        ImmutableList<JavaDLTerm> paramTerms,
                        JavaDLTerm resultTerm,
	    	        JavaDLTerm excTerm,
	    	        Map<LocationVariable,JavaDLTerm> atPres,
	    	        Services services);

    public JavaDLTerm getFreePost(LocationVariable heap,
                            ProgramVariable selfVar,
                            ImmutableList<ProgramVariable> paramVars,
                            ProgramVariable resultVar,
                            ProgramVariable excVar,
                            Map<LocationVariable,? extends ProgramVariable> atPreVars,
                            Services services);

    public JavaDLTerm getFreePost(LocationVariable heap,
                            JavaDLTerm heapTerm,
                            JavaDLTerm selfTerm,
                            ImmutableList<JavaDLTerm> paramTerms,
                            JavaDLTerm resultTerm,
                            JavaDLTerm excTerm,
                            Map<LocationVariable,JavaDLTerm> atPres,
                            Services services);

    public JavaDLTerm getFreePost(List<LocationVariable> heapContext,
                            Map<LocationVariable,JavaDLTerm> heapTerms,
                            JavaDLTerm selfTerm,
                            ImmutableList<JavaDLTerm> paramTerms,
                            JavaDLTerm resultTerm,
                            JavaDLTerm excTerm,
                            Map<LocationVariable,JavaDLTerm> atPres,
                            Services services);

    /**
      * Returns the model method definition for model method contracts
      */
    public JavaDLTerm getRepresentsAxiom(LocationVariable heap,
        ProgramVariable selfVar,
        ImmutableList<ProgramVariable> paramVars,
        ProgramVariable resultVar,
        Map<LocationVariable,? extends ProgramVariable> atPreVars,
        Services services);

    public JavaDLTerm getRepresentsAxiom(LocationVariable heap,
                                   JavaDLTerm heapTerm,
                                   JavaDLTerm selfTerm,
                                   ImmutableList<JavaDLTerm> paramTerms,
                                   JavaDLTerm resultTerm,
                                   JavaDLTerm excTerm,
                                   Map<LocationVariable,JavaDLTerm> atPres,
                                   Services services);

    public String getBaseName();
    public JavaDLTerm getPre();
    public JavaDLTerm getPost();
    public JavaDLTerm getMod();
    public JavaDLTerm getMby();
    public JavaDLTerm getSelf();
    public ImmutableList<JavaDLTerm> getParams();
    public JavaDLTerm getResult();
    public JavaDLTerm getExc();
    public KeYJavaType getSpecifiedIn();

    public boolean hasResultVar();
}
