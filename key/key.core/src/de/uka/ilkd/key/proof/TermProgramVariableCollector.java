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

package de.uka.ilkd.key.proof;

import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;

public class TermProgramVariableCollector extends DefaultVisitor {

    private final HashSet<LocationVariable> result = new LinkedHashSet<LocationVariable> ();
    private boolean containsNonRigidFunctionSymbol = false;
    private final Services services;
	private boolean containsAtMostDepPredAsNonRigid = true;

    
    public TermProgramVariableCollector(Services services) {
        this.services = services;
    }
        
    

    /** is called by the execPostOrder-method of a term 
     * @param t the Term to checked if it is a program variable and if true the
     * variable is added to the list of found variables
     */  
    public void visit(Term t) {
	if ( t.op() instanceof LocationVariable ) {
	    result.add ( (LocationVariable) t.op() );
	} else if (!t.op().isRigid()) {
		containsNonRigidFunctionSymbol = true;

		Namespace<Function> funcNames = services.getNamespaces().functions();
		final Operator noRaW = funcNames.lookup("noRaW");
		final Operator noWaR = funcNames.lookup("noWaR");
		final Operator noR = funcNames.lookup("noR");
		final Operator noW = funcNames.lookup("noW");
		if (t.op() == noRaW || t.op() == noWaR || t.op() == noR|| t.op() == noW) {
			containsAtMostDepPredAsNonRigid &= true;
		} else {
			containsAtMostDepPredAsNonRigid = false;
		}
	
	}
	
	if ( !t.javaBlock ().isEmpty() ) {
	    ProgramVariableCollector pvc
		= new ProgramVariableCollector ( t.javaBlock ().program (), services );
	    pvc.start();
	    result.addAll ( pvc.result () );
	}
    }

    public HashSet<LocationVariable> result() { 
	return result;
    }    
    
    public boolean containsNonRigidNonProgramVariableSymbol() {
    	return containsNonRigidFunctionSymbol;
    }
    
    public boolean containsAtMostDepPredAsNonRigid() {
    	return containsAtMostDepPredAsNonRigid;
    }
}

