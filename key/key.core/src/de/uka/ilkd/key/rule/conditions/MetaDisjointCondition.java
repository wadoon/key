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
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.SVSubstitute;
import org.key_project.common.core.logic.op.SchemaVariable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class MetaDisjointCondition extends VariableConditionAdapter {
        
    private final TermSV var1;
    private final TermSV var2;


    public MetaDisjointCondition(TermSV s1, TermSV s2) {
	this.var1 = s1;
	this.var2 = s2;
    }
    
    
    private static boolean clearlyDisjoint(JavaDLTerm t1, 
	    				   JavaDLTerm t2, 
	    				   Services services) {
	final LocSetLDT setLDT = services.getTheories().getLocSetLDT();
	if(t1.op() instanceof Function && ((Function)t1.op()).isUnique()
           && t2.op() instanceof Function && ((Function)t2.op()).isUnique()
           && !t1.equals(t2)) {
	    return true;
	} else if(t1.sort().equals(setLDT.targetSort()) 
		  && t2.sort().equals(setLDT.targetSort())) {
	    final ImmutableSet<JavaDLTerm> t1set = services.getTermBuilder().unionToSet(t1);
	    final ImmutableSet<JavaDLTerm> t2set = services.getTermBuilder().unionToSet(t2);

	    ImmutableSet<Operator> t1Ops 
	    	= DefaultImmutableSet.<Operator>nil();
	    ImmutableSet<Operator> t2Ops 
	    	= DefaultImmutableSet.<Operator>nil();
	    for(JavaDLTerm t : t1set) {
		if(t.op().equals(setLDT.getSingleton())
		   && t.sub(0).op() instanceof Function 
		   && ((Function)t.sub(0).op()).isUnique()) {
		    t1Ops = t1Ops.add(t.op());
		} else if(t.op().equals(setLDT.getEmpty())){
		    continue;
		} else {
		    return false;
		}
	    }
	    for(JavaDLTerm t : t2set) {
		if(t.op().equals(setLDT.getSingleton())
		   && t.sub(0).op() instanceof Function 
		   && ((Function)t.sub(0).op()).isUnique()) {
		    t2Ops = t2Ops.add(t.op());
		} else if(t.op().equals(setLDT.getEmpty())){
		    continue;
		} else {
		    return false;
		}
	    }
	    
	    return t1Ops.intersect(t2Ops).isEmpty();	    
	} else {
	    return false;
	}
    }
    

    @Override
    public boolean check(SchemaVariable var, 
			 SVSubstitute subst, 
			 SVInstantiations svInst,
			 Services services) {
	final JavaDLTerm s1Inst = (JavaDLTerm) svInst.getInstantiation(var1);
	final JavaDLTerm s2Inst = (JavaDLTerm) svInst.getInstantiation(var2);
	if(s1Inst == null || s2Inst == null) {
	    return true;
	} else {
	    return clearlyDisjoint(s1Inst, s2Inst, services);
	}
    }

    
    @Override    
    public String toString () {
	return ("\\metaDisjoint " + var1 + ", " + var2);
    }
}