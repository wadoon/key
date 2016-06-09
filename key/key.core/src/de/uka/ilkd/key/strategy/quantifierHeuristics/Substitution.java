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

import java.util.Iterator;

import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.services.TermServices;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.ClashFreeSubst;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.util.Debug;

/**
 * This class decribes a substitution,which store a map(varMap) from quantifiable 
 * variable to a term(instance).
 */
public class Substitution {
    private final ImmutableMap<QuantifiableVariable,JavaDLTerm> varMap;
    
    public Substitution(ImmutableMap<QuantifiableVariable,JavaDLTerm> map){
        varMap = map;
    }
    
    public ImmutableMap<QuantifiableVariable,JavaDLTerm> getVarMap(){
        return varMap;
    }
    
    public JavaDLTerm getSubstitutedTerm(QuantifiableVariable var){
    	return varMap.get(var);
    }
    
    public boolean isTotalOn(ImmutableSet<QuantifiableVariable> vars) {
        for (QuantifiableVariable var : vars) {
            if (!varMap.containsKey(var)) return false;
        }
        return true;
    }
    

    /**
     * @return true if every instance in the varMap does not contain variable. 
     */
    public boolean isGround() {
        final Iterator<QuantifiableVariable> it = varMap.keyIterator ();
        while ( it.hasNext () ) {
            final JavaDLTerm t = getSubstitutedTerm(it.next ()); 
            if ( t.freeVars ().size () != 0 ) {
            	Debug.out("evil free vars in term: " + t);
                return false;
            }
        }
        return true;
    }   
  
    
    public JavaDLTerm apply(JavaDLTerm t, TermServices services) {
        assert isGround() :
            "non-ground substitutions are not yet implemented: " + this;
        final Iterator<QuantifiableVariable> it = varMap.keyIterator ();
        while ( it.hasNext () ) {
            final QuantifiableVariable var = it.next ();
            final Sort quantifiedVarSort = var.sort ();
            final Function quantifiedVarSortCast =
                quantifiedVarSort.getCastSymbol (services);
            JavaDLTerm instance = getSubstitutedTerm( var );
            if ( !instance.sort ().extendsTrans ( quantifiedVarSort ) )
            	instance = services.getTermBuilder().func ( quantifiedVarSortCast, instance );
            t = applySubst ( var, instance, t, services );
        }
        return t;
    }

    private JavaDLTerm applySubst(QuantifiableVariable var, JavaDLTerm instance, JavaDLTerm t, TermServices services) {
        final ClashFreeSubst subst = new ClashFreeSubst ( var,  instance, services);
        return subst.apply ( t );
    }
    
    /**
     * Try to apply the substitution to a term, introducing casts if
     * necessary (may never be the case any more, XXX)
     */
    public JavaDLTerm applyWithoutCasts(JavaDLTerm t, TermServices services) {
        assert isGround() :
            "non-ground substitutions are not yet implemented: " + this;
        final Iterator<QuantifiableVariable> it = varMap.keyIterator ();
        while ( it.hasNext () ) {
            final QuantifiableVariable var = it.next ();
            JavaDLTerm instance = getSubstitutedTerm( var );
            
            try {
                t = applySubst ( var, instance, t, services );
            } catch (TermCreationException e) {
                final Sort quantifiedVarSort = var.sort ();                
                if ( !instance.sort ().extendsTrans ( quantifiedVarSort ) ) {
                    final Function quantifiedVarSortCast =
                        quantifiedVarSort.getCastSymbol (services);
                    instance = services.getTermBuilder().func ( quantifiedVarSortCast, instance );
                    t = applySubst ( var, instance, t, services );
                } else {
                    throw e;
                }
            }        
        }
        return t;
    }
    
    public boolean equals(Object arg0) {
        if ( !(arg0 instanceof Substitution) ) return false;
        final Substitution s = (Substitution)arg0;
        return varMap.equals(s.varMap);
    }

    public int hashCode() {
        return varMap.hashCode();
    }
    
    public String toString() {
    	return "" + varMap;
    }
    
    public boolean termContainsValue(JavaDLTerm term) {
        Iterator<JavaDLTerm> it = varMap.valueIterator ();
        while ( it.hasNext () ) {
            if ( recOccurCheck ( it.next (), term ) ) return true;
        }
        return false;
    }

    /**
     * check whether term "sub" is in term "term"
     */
    private boolean recOccurCheck(JavaDLTerm sub, JavaDLTerm term) {
        if ( sub.equals ( term ) ) return true;
        for ( int i = 0; i < term.arity (); i++ ) {
            if ( recOccurCheck ( sub, term.sub ( i ) ) ) return true;
        }
        return false;
    }
}