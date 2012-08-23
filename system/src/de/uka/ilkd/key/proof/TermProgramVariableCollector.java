// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.util.HashSet;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.visitor.IProgramVariableCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.init.IProgramVisitorProvider;

public class TermProgramVariableCollector extends Visitor {

    private final HashSet<LocationVariable> result = new HashSet<LocationVariable> ();
    private final IServices services;

    
    public TermProgramVariableCollector(IServices services) {
        this.services = services;
    }
        
    

    /** is called by the execPostOrder-method of a term 
     * @param t the Term to checked if it is a program variable and if true the
     * variable is added to the list of found variables
     */  
    public void visit(Term t) {
	if ( t.op() instanceof LocationVariable ) {
	    result.add ( (LocationVariable) t.op() );
	} 
	
	if ( !t.javaBlock ().isEmpty() ) {
	    IProgramVariableCollector<LocationVariable> pvc
		= IProgramVisitorProvider.getInstance().<LocationVariable>createProgramVariableCollector( t.javaBlock ().program (), services );
	    pvc.start();
	    result.addAll ( pvc.result () );
	}
    }

    public HashSet<LocationVariable> result() { 
	return result;
    }    
}
