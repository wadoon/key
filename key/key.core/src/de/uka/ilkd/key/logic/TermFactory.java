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

import org.key_project.common.core.logic.GenericTermFactory;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.op.TypeCheckingAndInferenceService;

/** 
 * The GenericTermFactory is the <em>only</em> way to create terms using constructors 
 * of class JavaDLTerm or any of its subclasses. It is the only class that implements 
 * and may exploit knowledge about sub classes of {@link JavaDLTerm}. All other 
 * classes of the system only know about terms what the {@link JavaDLTerm} class 
 * offers them. 
 * 
 * This class is used to encapsulate knowledge about the internal term 
 * structures.
 * See {@link de.uka.ilkd.key.logic.TermBuilder} for more convenient methods to 
 * create terms. 
 */
public final class TermFactory implements GenericTermFactory<JavaBlock, JavaDLTerm> {
    

    private static final ImmutableArray<JavaDLTerm> NO_SUBTERMS = new ImmutableArray<JavaDLTerm>();
    private final Map<JavaDLTerm, JavaDLTerm> cache;
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public TermFactory(Map<JavaDLTerm, JavaDLTerm> cache) {
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
    public JavaDLTerm createTerm(Operator op, 
	    		   ImmutableArray<JavaDLTerm> subs, 
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
    public JavaDLTerm createTerm(Operator op, 
	    		   ImmutableArray<JavaDLTerm> subs, 
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock) {

    	return createTerm(op, subs, boundVars, javaBlock, null);
    }

    @Override
    public JavaDLTerm createTerm(Operator op,
                           JavaDLTerm[] subs,
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock) {
	return createTerm(op, createSubtermArray(subs), boundVars, javaBlock, null);
    }
    
    @Override
    public JavaDLTerm createTerm(Operator op, JavaDLTerm... subs) {
        return createTerm(op, subs, null, null);
    }
    
    @Override
    public JavaDLTerm createTerm(Operator op,
                           JavaDLTerm[] subs,
                           ImmutableArray<QuantifiableVariable> boundVars,
                           JavaBlock javaBlock,
                           ImmutableArray<TermLabel> labels) {
    	return createTerm(op, createSubtermArray(subs), boundVars, javaBlock, labels);
    }

    @Override
    public JavaDLTerm createTerm(Operator op,
            JavaDLTerm[] subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            JavaBlock javaBlock,
            TermLabel label) {
        return createTerm(op, createSubtermArray(subs), boundVars,
                javaBlock, new ImmutableArray<TermLabel>(label));
    }

    @Override
    public JavaDLTerm createTerm(Operator op, JavaDLTerm[] subs, TermLabel label) {
        return createTerm(op, subs, null, null, label);
    }
   
    @Override
    public JavaDLTerm createTerm(Operator op, JavaDLTerm[] subs, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, createSubtermArray(subs), null, null, labels);
    }

    @Override
    public JavaDLTerm createTerm(Operator op, JavaDLTerm sub, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, new ImmutableArray<JavaDLTerm>(sub), null, null, labels);
    }    

    @Override
    public JavaDLTerm createTerm(Operator op, JavaDLTerm sub1, JavaDLTerm sub2, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, new JavaDLTerm[] { sub1, sub2 }, null, null, labels);
    }    

    @Override
    public JavaDLTerm createTerm(Operator op, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, NO_SUBTERMS, null, null, labels);
    }

    //-------------------------------------------------------------------------
    //private interface
    //-------------------------------------------------------------------------
    
    private ImmutableArray<JavaDLTerm> createSubtermArray(JavaDLTerm[] subs) {
        return subs == null || subs.length == 0 ? 
                NO_SUBTERMS : new ImmutableArray<JavaDLTerm>(subs);
    }

    private JavaDLTerm doCreateTerm(Operator op, ImmutableArray<JavaDLTerm> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            JavaBlock javaBlock, ImmutableArray<TermLabel> labels) {
        
        final Sort sort = TypeCheckingAndInferenceService.getTypeCheckerFor(op).sort(subs, op);
        
        final JavaDLTerm newTerm 
            = (labels == null || labels.isEmpty() ? 
                    new TermImpl(op, sort, subs, boundVars, javaBlock) : 
                new LabeledTermImpl(op, sort, subs, boundVars, javaBlock, labels));
        
        return cacheTerm(newTerm);
    }

    
    /**
     * Checks whether the JavaDLTerm is valid on the top level. If this is the case
     * this method returns the JavaDLTerm unmodified. Otherwise a
     * TermCreationException is thrown.
     * @param term the {@link JavaDLTerm} to be checked
     * @return the same term 
     * @throws TermCreationException if the term is not wellformed
     */
    public final JavaDLTerm checked(JavaDLTerm term) {
        final Operator op = term.op();
        if (TypeCheckingAndInferenceService.getTypeCheckerFor(op)
                .validTopLevel(term, op)) {
            return term;
        }
        else {
            throw new TermCreationException(op, term);
        }
    }
    
    private JavaDLTerm cacheTerm(final JavaDLTerm newTerm) {
        // Check if caching is possible. It is not possible if a non empty JavaBlock is available
        // in the term or in one of its children because the meta information like PositionInfos
        // may be different.
        if (!newTerm.containsModalContentRecursive()) {
           
           JavaDLTerm term;  
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
