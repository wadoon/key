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


import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.SVSubstitute;
import org.key_project.common.core.logic.op.SchemaVariable;
import org.key_project.common.core.services.TermServices;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class EqualUniqueCondition implements VariableCondition {
    private final TermSV t;
    private final TermSV t2;
    private final FormulaSV res;
    
    
    public EqualUniqueCondition(TermSV t, TermSV t2, FormulaSV res) {
        this.t = t;
        this.t2 = t2;
        this.res = res;
    }
    
    
    private static JavaDLTerm equalUnique(JavaDLTerm t1, JavaDLTerm t2, TermServices services) {
	if(!(t1.op() instanceof Function 
	     && t2.op() instanceof Function
	     && ((Function)t1.op()).isUnique()
	     && ((Function)t2.op()).isUnique())) {
	    return null;
	} else if(t1.op() == t2.op()) {
	    JavaDLTerm result = services.getTermBuilder().tt();
	    for(int i = 0, n = t1.arity(); i < n; i++) {
		result = services.getTermBuilder().and(result, services.getTermBuilder().equals(t1.sub(i), t2.sub(i)));
	    }
	    return result;
	} else {
	    return services.getTermBuilder().ff();
	}
    }
    
    
    @Override
    public MatchConditions check(SchemaVariable var, 
	    		  	 SVSubstitute instCandidate, 
	    		  	 MatchConditions mc, 
	    		  	 Services services) {
	SVInstantiations svInst = mc.getInstantiations();
	JavaDLTerm tInst   = (JavaDLTerm) svInst.getInstantiation(t);
	JavaDLTerm t2Inst  = (JavaDLTerm) svInst.getInstantiation(t2);
	JavaDLTerm resInst = (JavaDLTerm) svInst.getInstantiation(res);
	if(tInst == null || t2Inst == null) {
	    return mc;
	}
	
	JavaDLTerm properResInst = equalUnique(tInst, t2Inst, services);
	if(properResInst == null) {
	    return null;
	} else if(resInst == null) {
	    svInst = svInst.add(res, properResInst, services);
	    return mc.setInstantiations(svInst);
	} else if(resInst.equals(properResInst)) {
	    return mc;
	} else {
	    return null;
	}
    }
    

    @Override
    public String toString () {
        return "\\equalUnique (" + t + ", " + t2 + ", " + res + ")";
    }
}