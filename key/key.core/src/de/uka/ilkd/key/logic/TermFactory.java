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

import org.key_project.common.core.logic.CCTermFactory;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.op.TypeCheckingAndInferenceService;

/** 
 * The GenericTermFactory is the <em>only</em> way to create terms using constructors 
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
public final class TermFactory implements CCTermFactory<JavaBlock, Term> {
    

    private static final ImmutableArray<Term> NO_SUBTERMS = new ImmutableArray<Term>();
    private final Map<Term, Term> cache;
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
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
    @Override
    public Term createTerm(Operator op, 
	    		   ImmutableArray<Term> subs, 
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock,
			   ImmutableArray<TermLabel> labels) {
        if(op == null) {
            throw new TermCreationException("null-Operator at GenericTermFactory");
        }

        if (subs == null || subs.isEmpty()) {
            subs = NO_SUBTERMS;
        }
	
        return doCreateTerm(op, subs, boundVars, javaBlock, labels);
    }
    
    @Override
    public Term createTerm(Operator op, 
	    		   ImmutableArray<Term> subs, 
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock) {

    	return createTerm(op, subs, boundVars, javaBlock, null);
    }

    @Override
    public Term createTerm(Operator op,
                           Term[] subs,
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock) {
	return createTerm(op, createSubtermArray(subs), boundVars, javaBlock, null);
    }
    
    @Override
    public Term createTerm(Operator op, Term... subs) {
        return createTerm(op, subs, null, null);
    }
    
    @Override
    public Term createTerm(Operator op,
                           Term[] subs,
                           ImmutableArray<QuantifiableVariable> boundVars,
                           JavaBlock javaBlock,
                           ImmutableArray<TermLabel> labels) {
    	return createTerm(op, createSubtermArray(subs), boundVars, javaBlock, labels);
    }

    @Override
    public Term createTerm(Operator op,
            Term[] subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            JavaBlock javaBlock,
            TermLabel label) {
        return createTerm(op, createSubtermArray(subs), boundVars,
                javaBlock, new ImmutableArray<TermLabel>(label));
    }

    @Override
    public Term createTerm(Operator op, Term[] subs, TermLabel label) {
        return createTerm(op, subs, null, null, label);
    }
   
    @Override
    public Term createTerm(Operator op, Term[] subs, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, createSubtermArray(subs), null, null, labels);
    }

    @Override
    public Term createTerm(Operator op, Term sub, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, new ImmutableArray<Term>(sub), null, null, labels);
    }    

    @Override
    public Term createTerm(Operator op, Term sub1, Term sub2, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, new Term[] { sub1, sub2 }, null, null, labels);
    }    

    @Override
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
        
        final Sort sort = TypeCheckingAndInferenceService.getTypeCheckerFor(op).sort(subs, op);
        
        final Term newTerm 
            = (labels == null || labels.isEmpty() ? 
                    new TermImpl(op, sort, subs, boundVars, javaBlock) : 
                new LabeledTermImpl(op, sort, subs, boundVars, javaBlock, labels));
        
        return cacheTerm(newTerm);
    }

    
    /**
     * Checks whether the Term is valid on the top level. If this is the case
     * this method returns the Term unmodified. Otherwise a
     * TermCreationException is thrown.
     * @param term the {@link Term} to be checked
     * @return the same term 
     * @throws TermCreationException if the term is not wellformed
     */
    public final Term checked(Term term) {
        final Operator op = term.op();
        if (TypeCheckingAndInferenceService.getTypeCheckerFor(op)
                .validTopLevel(term, op)) {
            return term;
        }
        else {
            throw new TermCreationException(op, term);
        }
    }
    
    private Term cacheTerm(final Term newTerm) {
        // Check if caching is possible. It is not possible if a non empty JavaBlock is available
        // in the term or in one of its children because the meta information like PositionInfos
        // may be different.
        if (!newTerm.containsModalContentRecursive()) {
           
           Term term;  
           synchronized(cache) { 
               term = cache.get(newTerm);
           }
           if(term == null) {
               term = checked(newTerm);
               synchronized(cache) { 
                   cache.put(term, term);
               }
           }
           return term;
        }
        else {
           return checked(newTerm);
        }
    }
}
