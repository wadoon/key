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

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.UpdateApplication;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Quantifier;

class BasicMatching {
    
    private BasicMatching() {}
    
    /**
     * matching <code>trigger</code> to <code>targetTerm</code> recursively
     * @param trigger       a uni-trigger
     * @param targetTerm    a gound term
     * @return all substitution found from this matching
     */
    static ImmutableSet<Substitution> getSubstitutions(JavaDLTerm trigger, JavaDLTerm targetTerm) {
        ImmutableSet<Substitution> allsubs = DefaultImmutableSet.<Substitution>nil();
        if ( targetTerm.freeVars ().size () > 0
             || targetTerm.op () instanceof Quantifier ) return allsubs;
        final Substitution subst = match ( trigger, targetTerm );
        if ( subst != null ) allsubs = allsubs.add ( subst );
        final Operator op = targetTerm.op ();
        if ( !( op instanceof Modality || op instanceof UpdateApplication ) ) {
            for ( int i = 0; i < targetTerm.arity (); i++ )
                allsubs =
                    allsubs.union ( getSubstitutions ( trigger,
                                                       targetTerm.sub ( i ) ) );
        }
        return allsubs;
    }
    
    /**
   	 * @param pattern
   	 * @param instance
   	 * @return all substitution that a given pattern(ex: a term of a uniTrigger)
   	 * match in the instance. 
   	 */
	private static Substitution match(JavaDLTerm pattern, JavaDLTerm instance) {
        final ImmutableMap<QuantifiableVariable,JavaDLTerm> map =
            matchRec ( DefaultImmutableMap.<QuantifiableVariable,JavaDLTerm>nilMap(),
                       pattern, instance );
        if ( map == null ) return null;
        return new Substitution ( map );
    }
        
	/**
	 * match the pattern to instance recursively.
	 */
	private static ImmutableMap<QuantifiableVariable,JavaDLTerm>
                   matchRec(ImmutableMap<QuantifiableVariable,JavaDLTerm> varMap,
                            JavaDLTerm pattern, JavaDLTerm instance) {
		final Operator patternOp = pattern.op ();
    
		if ( patternOp instanceof QuantifiableVariable )
			return mapVarWithCheck (varMap,
                                    (QuantifiableVariable)patternOp, instance);
        
		if ( patternOp != instance.op() ) return null;
        for ( int i = 0; i < pattern.arity (); i++ ) {
            varMap = matchRec ( varMap, pattern.sub ( i ), instance.sub ( i ) );
            if ( varMap == null ) return null;
        }
        return varMap;
	}

	/**
	 * match a variable to a instance. 
	 *  @return true if it is a new vaiable or the instance it matched is
     *  the same as that it matched before.
	 */
	private static ImmutableMap<QuantifiableVariable,JavaDLTerm>
                   mapVarWithCheck(ImmutableMap<QuantifiableVariable,JavaDLTerm> varMap,
                                   QuantifiableVariable var, JavaDLTerm instance) {
		final JavaDLTerm oldTerm = varMap.get ( var );
        if ( oldTerm == null ) return varMap.put ( var, instance );

        if ( oldTerm.equals ( instance ) ) return varMap;
        return null;
	}


}