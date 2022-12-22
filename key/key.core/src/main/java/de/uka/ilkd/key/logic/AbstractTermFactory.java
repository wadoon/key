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

import java.util.List;
import java.util.Map;
import java.util.Optional;

import javax.annotation.Nonnull;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/**
 * The AbstractTermFactory is the <em>only</em> way to create terms using constructors
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
public abstract class AbstractTermFactory {
    /**
     * if termFactoryArt == false => TeeTermFactory is created otherwise FlatTermFActory is created
     * */
    static boolean termFactoryType = false ;
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public static AbstractTermFactory getTermFactory(){
        if(!termFactoryType){
            return new TreeTermFactory();
        }else{
            return new FlatTermFactory();
        }
    }
    //return new TreeTermFactory(cache);
    public static AbstractTermFactory getTermFactory(Map<Term, Term> cache){
        if(!termFactoryType){
            return new TreeTermFactory(cache);
        }else{
            return new FlatTermFactory(cache);
        }
    }
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------



    /**
     * Master method for term creation. Should be the only place where terms
     * are created in the entire system.
     */
    public abstract Term createTerm(Operator op,
	    		   ImmutableArray<Term> subs,
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock,
			   ImmutableArray<TermLabel> labels);

    public abstract Term createTerm(Operator op,
	    		   ImmutableArray<Term> subs,
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock);

    public abstract Term createTerm(Operator op,
                           Term[] subs,
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock);


    public abstract Term createTerm(Operator op, Term... subs);

    public abstract Term createTerm(Operator op,
                           Term[] subs,
                           ImmutableArray<QuantifiableVariable> boundVars,
                           JavaBlock javaBlock,
                           ImmutableArray<TermLabel> labels);

    public abstract Term createTerm(Operator op,
            Term[] subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            JavaBlock javaBlock,
            TermLabel label);

    public abstract Term createTerm(Operator op, Term[] subs, TermLabel label);

    public abstract Term createTerm(Operator op, Term[] subs, ImmutableArray<TermLabel> labels);

    public abstract Term createTerm(Operator op, Term sub, ImmutableArray<TermLabel> labels);

    public abstract Term createTerm(Operator op, Term sub1, Term sub2, ImmutableArray<TermLabel> labels);


    public abstract Term createTerm(Operator op, ImmutableArray<TermLabel> labels);
    /**
     * Reduce the given list of terms into a one term by using the operator.
     * The reduction is left-associative. e.g., the result is
     * {@code ((a op b) op c) op d }.
     *
     * @param junctor the left-associative operator to combine the terms together
     * @param terms a list of non-null temrs
     */
    public abstract @Nonnull Term createTerm(@Nonnull  Operator junctor, @Nonnull List<Term> terms);
}
