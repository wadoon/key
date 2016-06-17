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

import java.util.Set;

import org.key_project.common.core.logic.op.*;

import de.uka.ilkd.key.java.JavaDLTermServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class DropEffectlessElementariesCondition 
						implements VariableCondition {
    private final UpdateSV u;
    private final SchemaVariable x;
    private final SchemaVariable result;
    
    public DropEffectlessElementariesCondition(UpdateSV u,
	                               	       SchemaVariable x,
	                               	       SchemaVariable x2) {
	this.u = u;
	this.x = x;
	this.result = x2;
    }
    
    
    private static JavaDLTerm dropEffectlessElementariesHelper(
	    				JavaDLTerm update, 
	    				Set<LocationVariable> relevantVars, JavaDLTermServices services) {
	if(update.op() instanceof ElementaryUpdate) {
	    ElementaryUpdate eu = (ElementaryUpdate) update.op();
	    LocationVariable lhs = (LocationVariable) eu.lhs();
	    if(relevantVars.contains(lhs)) {
	        relevantVars.remove(lhs);
	        // removed, see bug #1269 (MU, CS)
//	        // updates of the form "x:=x" can be discarded (MU,CS)
//	        if(lhs.equals(update.sub(0).op())) {
//	            return TB.skip();
//	        }
		return null;
	    } else {
		return services.getTermBuilder().skip();
	    }
	} else if(update.op() == UpdateJunctor.PARALLEL_UPDATE) {
	    JavaDLTerm sub0 = update.sub(0);
            JavaDLTerm sub1 = update.sub(1);
            // first descend to the second sub-update to keep relevantVars in
            // good order
	    JavaDLTerm newSub1 = dropEffectlessElementariesHelper(sub1, relevantVars, services);
	    JavaDLTerm newSub0 = dropEffectlessElementariesHelper(sub0, relevantVars, services);
	    if(newSub0 == null && newSub1 == null) {
		return null;
	    } else {
		newSub0 = newSub0 == null ? sub0 : newSub0;
		newSub1 = newSub1 == null ? sub1 : newSub1;
		return services.getTermBuilder().parallel(newSub0, newSub1);
	    }
	} else if(update.op() == UpdateApplication.UPDATE_APPLICATION) {
	    JavaDLTerm sub0 = update.sub(0);
	    JavaDLTerm sub1 = update.sub(1);
	    JavaDLTerm newSub1 = dropEffectlessElementariesHelper(sub1, relevantVars, services);
	    return newSub1 == null ? null : services.getTermBuilder().apply(sub0, newSub1, null);
	} else {
	    return null;
	}
    }    
    
    
    private static JavaDLTerm dropEffectlessElementaries(JavaDLTerm update, 
	    					   JavaDLTerm target,
	    					   Services services) {
	TermProgramVariableCollector collector 
		= services.getProgramServices().getFactory().create(services);
	target.execPostOrder(collector);
	Set<LocationVariable> varsInTarget = collector.result();
	JavaDLTerm simplifiedUpdate = dropEffectlessElementariesHelper(update, 
							         varsInTarget, services); 
	return simplifiedUpdate == null 
	       ? null 
	       : services.getTermBuilder().apply(simplifiedUpdate, target, null); 
    }
    
    


   @Override
    public MatchConditions check(SchemaVariable var, 
	    		  	 SVSubstitute instCandidate, 
	    		  	 MatchConditions mc, 
	    		  	 Services services) {
	SVInstantiations svInst = mc.getInstantiations();
	JavaDLTerm uInst      = (JavaDLTerm) svInst.getInstantiation(u);
	JavaDLTerm xInst      = (JavaDLTerm) svInst.getInstantiation(x);
	JavaDLTerm resultInst = (JavaDLTerm) svInst.getInstantiation(result);
	if(uInst == null || xInst == null) {
	    return mc;
	}
	
	JavaDLTerm properResultInst = dropEffectlessElementaries(uInst, 
						           xInst, 
						           services);
	if(properResultInst == null) {
	    return null;
	} else if(resultInst == null) {
	    svInst = svInst.add(result, properResultInst, services);
	    return mc.setInstantiations(svInst);
	} else if(resultInst.equals(properResultInst)) {
	    return mc;
	} else {
	    return null;
	}
    }
    
    
    @Override
    public String toString () {
        return "\\dropEffectlessElementaries(" 
               + u + ", " + x + ", " + result + ")";
    }
}