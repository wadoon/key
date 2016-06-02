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

import org.key_project.common.core.logic.DLTermFactory;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/** 
 * The TermFactory is the <em>only</em> way to create terms using constructors 
 * of class Term or any of its subclasses. It is the only class that implements 
 * and may exploit knowledge about sub classes of {@link Term}. All other 
 * classes of the system only know about terms what the {@link Term} class 
 * offers them. 
 * 
 * This class is used to encapsulate knowledge about the internal term 
 * structures.
 * See {@link org.key_project.common.core.logic.TermBuilder} for more convenient methods to 
 * create terms. 
 */
public final class TermFactory implements DLTermFactory<Sort, Term, Operator, JavaBlock, QuantifiableVariable> {
    

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
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.DLTermFactory#createTerm(de.uka.ilkd.key.logic.op.Operator, org.key_project.util.collection.ImmutableArray, org.key_project.util.collection.ImmutableArray, de.uka.ilkd.key.logic.JavaBlock, org.key_project.util.collection.ImmutableArray)
     */
    @Override
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
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.DLTermFactory#createTerm(de.uka.ilkd.key.logic.op.Operator, org.key_project.util.collection.ImmutableArray, org.key_project.util.collection.ImmutableArray, de.uka.ilkd.key.logic.JavaBlock)
     */
    @Override
    public Term createTerm(Operator op, 
	    		   ImmutableArray<Term> subs, 
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock) {

    	return createTerm(op, subs, boundVars, javaBlock, null);
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.DLTermFactory#createTerm(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.logic.Term[], org.key_project.util.collection.ImmutableArray, de.uka.ilkd.key.logic.JavaBlock)
     */
    @Override
    public Term createTerm(Operator op,
                           Term[] subs,
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock) {
	return createTerm(op, createSubtermArray(subs), boundVars, javaBlock, null);
    }
    
 
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.DLTermFactory#createTerm(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.logic.Term)
     */
    @Override
    public Term createTerm(Operator op, Term... subs) {
        return createTerm(op, subs, null, null);
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.DLTermFactory#createTerm(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.logic.Term[], org.key_project.util.collection.ImmutableArray, de.uka.ilkd.key.logic.JavaBlock, org.key_project.util.collection.ImmutableArray)
     */
    @Override
    public Term createTerm(Operator op,
                           Term[] subs,
                           ImmutableArray<QuantifiableVariable> boundVars,
                           JavaBlock javaBlock,
                           ImmutableArray<TermLabel> labels) {
    	return createTerm(op, createSubtermArray(subs), boundVars, javaBlock, labels);
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.DLTermFactory#createTerm(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.logic.Term[], org.key_project.util.collection.ImmutableArray, de.uka.ilkd.key.logic.JavaBlock, de.uka.ilkd.key.logic.label.TermLabel)
     */
    @Override
    public Term createTerm(Operator op,
            Term[] subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            JavaBlock javaBlock,
            TermLabel label) {
        return createTerm(op, createSubtermArray(subs), boundVars,
                javaBlock, new ImmutableArray<TermLabel>(label));
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.DLTermFactory#createTerm(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.logic.Term[], de.uka.ilkd.key.logic.label.TermLabel)
     */
    @Override
    public Term createTerm(Operator op, Term[] subs, TermLabel label) {
        return createTerm(op, subs, null, null, label);
    }
       
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.DLTermFactory#createTerm(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.logic.Term[], org.key_project.util.collection.ImmutableArray)
     */
    @Override
    public Term createTerm(Operator op, Term[] subs, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, createSubtermArray(subs), null, null, labels);
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.DLTermFactory#createTerm(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.logic.Term, org.key_project.util.collection.ImmutableArray)
     */
    @Override
    public Term createTerm(Operator op, Term sub, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, new ImmutableArray<Term>(sub), null, null, labels);
    }    

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.DLTermFactory#createTerm(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.logic.Term, de.uka.ilkd.key.logic.Term, org.key_project.util.collection.ImmutableArray)
     */
    @Override
    public Term createTerm(Operator op, Term sub1, Term sub2, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, new Term[]{sub1, sub2}, null, null, labels);
    }    


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.DLTermFactory#createTerm(de.uka.ilkd.key.logic.op.Operator, org.key_project.util.collection.ImmutableArray)
     */
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
        final Term newTerm 
            = (labels == null || labels.isEmpty() ? 
                    new TermImpl(op, subs, boundVars, javaBlock) : 
                new LabeledTermImpl(op, subs, boundVars, javaBlock, labels)).checked();
        // Check if caching is possible. It is not possible if a non empty JavaBlock is available
        // in the term or in one of its children because the meta information like PositionInfos
        // may be different.
        if (!newTerm.isContainsJavaBlockRecursive()) {
           
           Term term;  
           synchronized(cache) { 
               term = cache.get(newTerm);
           }
           if(term == null) {
               term = newTerm;
               synchronized(cache) { 
                   cache.put(term, term);
               }
           }
           return term;
        }
        else {
           return newTerm;
        }
    }
}
