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

package de.uka.ilkd.key.logic;

import java.util.Map;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/** 
 * The TermFactory is the <em>only</em> way to create terms using constructors 
 * of class Term or any of its subclasses. It is the only class that implements 
 * and may exploit knowledge about sub classes of {@link Term}. All other 
 * classes of the system only know about terms what the {@link Term} class 
 * offers them. 
 * 
 * This class is used to encapsulate knowledge about the internal term 
 * structures.
 * See {@link de.uka.ilkd.key.logic.TermBuilder} for more convenient methods to 
 * create terms. 
 */
public final class TermFactory {
    

    private static final ImmutableArray<Term> NO_SUBTERMS = new ImmutableArray<Term>();
    private final Map<CacheKey, Term> cache;
    
    private final TermFactory noCache;
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    private TermFactory() {
        this.cache = null;
        this.noCache = this;
    }
    
    public TermFactory(Map<CacheKey, Term> cache) {
        this.cache = cache;
        this.noCache = new TermFactory();
    }
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Master method for term creation. Should be the only place where terms 
     * are created in the entire system.
     */
    public Term createTerm(Operator op, 
	    		   ImmutableArray<Term> subs, 
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock,
			   ImmutableArray<TermLabel> labels) {
        if(op == null) {
            throw new TermCreationException("null-Operator at TermFactory");
        }

        if (subs == null || subs.isEmpty()) {
            subs = NO_SUBTERMS;
        }
	
        return doCreateTerm(op, subs, boundVars, javaBlock, labels);
    }
    
    public Term createTerm(Operator op, 
	    		   ImmutableArray<Term> subs, 
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock) {

    	return createTerm(op, subs, boundVars, javaBlock, null);
    }


    public Term createTerm(Operator op,
                           Term[] subs,
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock) {
	return createTerm(op, createSubtermArray(subs), boundVars, javaBlock, null);
    }
    
 
    public Term createTerm(Operator op, Term... subs) {
        return createTerm(op, subs, null, null);
    }
    
    public Term createTerm(Operator op,
                           Term[] subs,
                           ImmutableArray<QuantifiableVariable> boundVars,
                           JavaBlock javaBlock,
                           ImmutableArray<TermLabel> labels) {
    	return createTerm(op, createSubtermArray(subs), boundVars, javaBlock, labels);
    }

    public Term createTerm(Operator op,
            Term[] subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            JavaBlock javaBlock,
            TermLabel label) {
        return createTerm(op, createSubtermArray(subs), boundVars,
                javaBlock, new ImmutableArray<TermLabel>(label));
    }

    public Term createTerm(Operator op, Term[] subs, TermLabel label) {
        return createTerm(op, subs, null, null, label);
    }
       
    public Term createTerm(Operator op, Term[] subs, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, createSubtermArray(subs), null, null, labels);
    }

    public Term createTerm(Operator op, Term sub, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, new ImmutableArray<Term>(sub), null, null, labels);
    }    

    public Term createTerm(Operator op, Term sub1, Term sub2, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, new Term[]{sub1, sub2}, null, null, labels);
    }    


    public Term createTerm(Operator op, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, NO_SUBTERMS, null, null, labels);
    }

    //-------------------------------------------------------------------------
    //private interface
    //-------------------------------------------------------------------------
    
    private ImmutableArray<Term> createSubtermArray(Term[] subs) {
        return subs == null || subs.length == 0 ? 
                NO_SUBTERMS : new ImmutableArray<Term>(subs);
    }

    private Term doCreateTerm(Operator op, ImmutableArray<Term> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            JavaBlock javaBlock, ImmutableArray<TermLabel> labels) {
        // Check if caching is possible. It is not possible if a non empty JavaBlock is available
        // in the term or in one of its children because the meta information like PositionInfos
        // may be different.
        if (cache != null && ((javaBlock == null || javaBlock == JavaBlock.EMPTY_JAVABLOCK) &&
                !containsJavaBlockRecursive(subs))) {
           final CacheKey key = new CacheKey(op, subs, boundVars, labels); 
           Term term; 
           synchronized(cache) { 
               term = cache.get(key);
           }
           if (term == null) {
               term = (labels == null || labels.isEmpty() ? 
                       new TermImpl(op, subs, boundVars, javaBlock) : 
                   new LabeledTermImpl(op, subs, boundVars, javaBlock, labels)).checked();
               synchronized(cache) { 
                   cache.put(key, term);
               }
           }
           return term;
        }
        else {
            final Term newTerm 
            = (labels == null || labels.isEmpty() ? 
                    new TermImpl(op, subs, boundVars, javaBlock) : 
                new LabeledTermImpl(op, subs, boundVars, javaBlock, labels)).checked();
           return newTerm;
        }
    }
    
    private final boolean containsJavaBlockRecursive(ImmutableArray<Term> subs) {
        if (subs != null && subs.size() > 0) {
            for (int i = 0, sz = subs.size(); i<sz; i++) {
                if (subs.get(i).containsJavaBlockRecursive()) {
                    return true;
                }
            }
        }
        return false;
    }

    public static class CacheKey {
        final static private ImmutableArray<QuantifiableVariable> NO_BOUND_VARS = new ImmutableArray<>();
        final static private ImmutableArray<TermLabel> NO_LABELS = new ImmutableArray<>();
        final Operator op;
        final ImmutableArray<Term> subs;
        final ImmutableArray<QuantifiableVariable> boundVars;
        final ImmutableArray<TermLabel> labels;
        
        private int hashCode = -1;
        
        public CacheKey(Operator op, ImmutableArray<Term> subs,
                ImmutableArray<QuantifiableVariable> boundVars,
                ImmutableArray<TermLabel> labels) {
            this.op = op;
            this.subs = subs == null ? NO_SUBTERMS : subs;
            this.boundVars = boundVars == null ? NO_BOUND_VARS : boundVars;
            this.labels = labels == null ? NO_LABELS : labels;
            hashCode();
        }

        @Override
        public int hashCode() {
            if (hashCode == -1) {            
                final int prime = 31;
                int result = prime + boundVars.hashCode();                
                result = prime * result +  labels.hashCode();
                result = prime * result + op.hashCode();
                result = prime * result + subs.hashCode();
                if (result == -1) { 
                    hashCode = 0;
                }
                else { 
                    hashCode = result;
                }
            }
            return hashCode;
        }

        @Override
        public boolean equals(Object obj) {
            CacheKey other = (CacheKey) obj;
            if (!op.equals(other.op)) {
                return false;
            }
            if (!boundVars.equals(other.boundVars)) {
                return false;            
            } 
            if (!labels.equals(other.labels)) {
                return false;
            }
            if (!subs.equals(other.subs)) {
                return false;
            }
            return true;
        }
        
    }

    public TermFactory noCacheTermFactory() {
        return noCache;
    }
}
