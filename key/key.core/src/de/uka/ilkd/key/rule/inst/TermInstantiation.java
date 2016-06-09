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

package de.uka.ilkd.key.rule.inst;

import org.key_project.common.core.logic.op.SchemaVariable;

import de.uka.ilkd.key.logic.JavaDLTerm;

/** This class is used to store the instantiation of a schemavarible
 * if it is a term.
 */
public class TermInstantiation extends InstantiationEntry<JavaDLTerm> {

    private static final RigidnessException RIGIDNESS_EXCEPTION 
    	= new RigidnessException( 
    		"Tried to instantiate a rigid schema variable"
    		+ " with a non-rigid term/formula" );

    
    /** creates a new ContextInstantiationEntry 
     * @param sv the SchemaVariable that is instantiated
     * @param term the JavaDLTerm the SchemaVariable is instantiated with
     */
    TermInstantiation(SchemaVariable sv, JavaDLTerm term) {
	super(term);
	//TODO: Remove the check below and move it to the matching logic
	//Done for VM based matching
	if(!term.isRigid () && sv.isRigid()) {
	    throw RIGIDNESS_EXCEPTION;
	}
    }
}