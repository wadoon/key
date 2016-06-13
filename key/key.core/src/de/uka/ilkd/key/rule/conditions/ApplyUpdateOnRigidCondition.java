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

package de.uka.ilkd.key.rule.conditions;

import org.key_project.common.core.logic.op.SVSubstitute;
import org.key_project.common.core.logic.op.SchemaVariable;

import de.uka.ilkd.key.java.JavaDLTermServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class ApplyUpdateOnRigidCondition implements VariableCondition {
    
    private final UpdateSV u;
    private final SchemaVariable x;
    private final SchemaVariable x2;
    
    public ApplyUpdateOnRigidCondition(UpdateSV u,
	                               SchemaVariable x,
	                               SchemaVariable x2) {
	this.u = u;
	this.x = x;
	this.x2 = x2;
    }
    
    
    private static JavaDLTerm applyUpdateOnRigid(JavaDLTerm update, JavaDLTerm target, JavaDLTermServices services) {
	JavaDLTerm[] updatedSubs = new JavaDLTerm[target.arity()];
	for(int i = 0; i < updatedSubs.length; i++) {
	    updatedSubs[i] = services.getTermBuilder().apply(update, target.sub(i), null);
	}
	JavaDLTerm result = services.getTermFactory().createTerm(target.op(), 
				         updatedSubs,
				         target.boundVars(), 
				         target.modalContent());
	return result;
    }
    
    
    @Override
    public MatchConditions check(SchemaVariable var, 
	    		  	 SVSubstitute instCandidate, 
	    		  	 MatchConditions mc, 
	    		  	 Services services) {
	SVInstantiations svInst = mc.getInstantiations();
	JavaDLTerm uInst  = (JavaDLTerm) svInst.getInstantiation(u);
	JavaDLTerm xInst  = (JavaDLTerm) svInst.getInstantiation(x);
	JavaDLTerm x2Inst = (JavaDLTerm) svInst.getInstantiation(x2);
	if(uInst == null || xInst == null) {
	    return mc;
	}
	
	if(!xInst.op().isRigid() || xInst.op().arity() == 0) {
	    return null;
	}
	
	JavaDLTerm properX2Inst = applyUpdateOnRigid(uInst, xInst, services);
	if(x2Inst == null) {
	    svInst = svInst.add(x2, properX2Inst, services);
	    return mc.setInstantiations(svInst);
	} else if(x2Inst.equals(properX2Inst)) {
	    return mc;
	} else {
	    return null;
	}
    }
    
    
    @Override
    public String toString () {
        return "\\applyUpdateOnRigid(" + u + ", " + x + ", " + x2 + ")";
    }
}