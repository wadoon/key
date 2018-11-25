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
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.ReadLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.WriteLock;

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
    private final Map<Term, Term> cache;
    /**
     * 
     * read/write lock for cache access to avoid unnecessary locking
     */
    private final ReentrantReadWriteLock rw_lock = new ReentrantReadWriteLock();
    private final ReadLock read_lock = rw_lock.readLock();
    private final WriteLock write_lock = rw_lock.writeLock();

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    
    public TermFactory() {
        this.cache = null;
    }
    
    public TermFactory(Map<Term, Term> cache) {
        this.cache = cache;
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
        final TermImpl newTerm 
            = (labels == null || labels.isEmpty() ? 
                    new TermImpl(op, subs, boundVars, javaBlock) : 
                new LabeledTermImpl(op, subs, boundVars, javaBlock, labels));
        // Check if caching is possible. It is not possible if a non empty JavaBlock is available
        // in the term or in one of its children because the meta information like PositionInfos
        // may be different.
        if (cache != null && !newTerm.containsJavaBlockRecursive()) {
           Term term;          
           try {
               read_lock.lock();
               term = cache.get(newTerm);
           } finally { 
               read_lock.unlock();
           }
           if(term == null) {
               try { 
                   write_lock.lock();
                   term = cache.putIfAbsent(newTerm, newTerm);                   
               } finally {
                   write_lock.unlock();
               }
               if (term == null) {
                   term = newTerm.checked(); // check if well-typed
               }
           }
           return term;
        }
        else {
           return newTerm.checked();
        }
    }
}
