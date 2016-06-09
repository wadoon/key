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

package de.uka.ilkd.key.speclang;

import java.util.Map;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.util.InfFlowSpec;



/**
 * A loop invariant, consisting of an invariant formula, a set of loop 
 * predicates, a modifies clause, and a variant term.
 */
public interface LoopInvariant extends SpecificationElement {

    /**
     * Returns the loop to which the invariant belongs.
     */
    public LoopStatement getLoop();

    /**
     * Returns the contracted function symbol.
     */
    public IProgramMethod getTarget();

    /** Returns the invariant formula. */
    public JavaDLTerm getInvariant(LocationVariable heap, JavaDLTerm selfTerm,
                             Map<LocationVariable,JavaDLTerm> atPres, Services services);

    public JavaDLTerm getInvariant(JavaDLTerm selfTerm, Map<LocationVariable,JavaDLTerm> atPres, Services services);

    public JavaDLTerm getInvariant(Services services);

    /**
     * Returns the modifies clause.
     */
    public JavaDLTerm getModifies(LocationVariable heap, JavaDLTerm selfTerm,
                            Map<LocationVariable,JavaDLTerm> atPres, Services services);

    public JavaDLTerm getModifies(JavaDLTerm selfTerm, Map<LocationVariable,JavaDLTerm> atPres, Services services);

    /**
     * Returns the information flow specification clause.
     */
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap);

    public ImmutableList<InfFlowSpec> getInfFlowSpecs(Services services);

    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap,
                                                      JavaDLTerm selfTerm,
                                                      Map<LocationVariable, JavaDLTerm> atPres,
                                                      Services services);

    public boolean hasInfFlowSpec(Services services);

    /**
     * Returns the variant term. 
     */
    public JavaDLTerm getVariant(JavaDLTerm selfTerm, 
            		   Map<LocationVariable,JavaDLTerm> atPres,
            		   Services services);

    /**
     * Returns the term internally used for self.
     * Use with care - it is likely that this is *not* the right "self" for you.
     */
    public JavaDLTerm getInternalSelfTerm();

    public JavaDLTerm getModifies();

    /**
     * Returns operators internally used for the pre-heap.
     */
    public Map<LocationVariable,JavaDLTerm> getInternalAtPres();

    /**
     * Returns the term internally used for the invariant. 
     * Use with care - it is likely that this is *not* the right "self" for you.
     */
    public Map<LocationVariable,JavaDLTerm> getInternalInvariants();

    /**
     * Returns the term internally used for the variant. 
     * Use with care - it is likely that this is *not* the right "self" for you.
     */
    public JavaDLTerm getInternalVariant();

    public Map<LocationVariable,JavaDLTerm> getInternalModifies();

    public Map<LocationVariable,
               ImmutableList<InfFlowSpec>> getInternalInfFlowSpec();

    public LoopInvariant create(LoopStatement loop,
                                IProgramMethod pm,
                                KeYJavaType kjt,
                                Map<LocationVariable,JavaDLTerm> invariants,
                                Map<LocationVariable,JavaDLTerm> modifies,
                                Map<LocationVariable,
                                    ImmutableList<InfFlowSpec>> infFlowSpecs,
                                JavaDLTerm variant,
                                JavaDLTerm selfTerm,
                                ImmutableList<JavaDLTerm> localIns,
                                ImmutableList<JavaDLTerm> localOuts,
                                Map<LocationVariable,JavaDLTerm> atPres);

    public LoopInvariant create(LoopStatement loop,
                                Map<LocationVariable,JavaDLTerm> invariants,
                                Map<LocationVariable,JavaDLTerm> modifies,
                                Map<LocationVariable,
                                    ImmutableList<InfFlowSpec>> infFlowSpecs,
                                JavaDLTerm variant,
                                JavaDLTerm selfTerm,
                                ImmutableList<JavaDLTerm> localIns,
                                ImmutableList<JavaDLTerm> localOuts,
                                Map<LocationVariable,JavaDLTerm> atPres);

    public LoopInvariant instantiate(Map<LocationVariable,JavaDLTerm> invariants, JavaDLTerm variant);

    public LoopInvariant configurate(Map<LocationVariable,JavaDLTerm> invariants,
                                     Map<LocationVariable,JavaDLTerm> modifies,
                                     Map<LocationVariable,
                                         ImmutableList<InfFlowSpec>> infFlowSpecs,
                                     JavaDLTerm variant);

    /**
     * Returns a new loop invariant where the loop reference has been
     * replaced with the passed one.
     */
    public LoopInvariant setLoop(LoopStatement loop);

    public LoopInvariant setTarget(IProgramMethod newPM);

    /**
     * Returns a new loop invariant where the invariant formula has been
     * replaced with the passed one. Take care: the variables used for
     * the receiver, parameters, and local variables must stay the same!
     */
    public LoopInvariant setInvariant(Map<LocationVariable,JavaDLTerm> invariants, 
            			      JavaDLTerm selfTerm,
            			      Map<LocationVariable,JavaDLTerm> atPres,
            			      Services services); 

    /** 
     * Loop invariants can be visited like source elements:
     * This method calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element.
     */
    public void visit(Visitor v);
    
    /**
     * Returns the invariant in pretty plain text format.
     */
    public String getPlainText(Services services, Iterable<LocationVariable> heapContext, boolean usePrettyPrinting, boolean useUnicodeSymbols);

    public String getUniqueName();

    public KeYJavaType getKJT();

    public LoopInvariant setTarget(KeYJavaType newKJT, IObserverFunction newPM);

    /**
     * Returns the original Self Variable to replace it easier.
     */
    public OriginalVariables getOrigVars();
}