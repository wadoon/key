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

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.util.InfFlowSpec;

/**
 * Standard implementation of the LoopInvariant interface.
 */
public final class LoopInvariantImpl implements LoopInvariant {

    private final LoopStatement loop;
    private final IProgramMethod pm;
    private final KeYJavaType kjt;
    private final Map<LocationVariable,JavaDLTerm> originalInvariants;
    private final Map<LocationVariable,JavaDLTerm> originalModifies;
    private final Map<LocationVariable,
                      ImmutableList<InfFlowSpec>> originalInfFlowSpecs;
    private final JavaDLTerm originalVariant;
    private final JavaDLTerm originalSelfTerm;
    private final ImmutableList<JavaDLTerm> localIns;
    private final ImmutableList<JavaDLTerm> localOuts;
    private final Map<LocationVariable,JavaDLTerm> originalAtPres;
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    /**
     * Creates a loop invariant.
     * @param loop the loop to which the invariant belongs
     * @param invariant the invariant formula
     * @param modifies the modifier set
     * @param infFlowSpecs low variables for information flow
     * @param variant the variant term
     * @param selfTerm the term used for the receiver object
     * @param heapAtPre the term used for the at pre heap
     */
    public LoopInvariantImpl(LoopStatement loop,
                             IProgramMethod pm,
                             KeYJavaType kjt,
                             Map<LocationVariable, JavaDLTerm> invariants,
                             Map<LocationVariable, JavaDLTerm> modifies,
                             Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs,
                             JavaDLTerm variant,
                             JavaDLTerm selfTerm,
                             ImmutableList<JavaDLTerm> localIns,
                             ImmutableList<JavaDLTerm> localOuts,
                             Map<LocationVariable, JavaDLTerm> atPres) {
        assert loop != null;
        //assert modifies != null;
        //assert heapAtPre != null;
        this.loop                       = loop;
        this.pm                         = pm;
        this.kjt                        = kjt;
        this.originalInvariants         =
                invariants == null ? new LinkedHashMap<LocationVariable,JavaDLTerm>() : invariants;
        this.originalVariant            = variant;
        this.originalModifies           =
                modifies == null ? new LinkedHashMap<LocationVariable,JavaDLTerm>() : modifies;
        this.originalInfFlowSpecs       =
                infFlowSpecs == null ? new LinkedHashMap<LocationVariable,
                                                         ImmutableList<InfFlowSpec>>()
                                     : infFlowSpecs;
        this.originalSelfTerm           = selfTerm;
        this.localIns                   = localIns;
        this.localOuts                  = localOuts;
        this.originalAtPres             =
                atPres == null ? new LinkedHashMap<LocationVariable,JavaDLTerm>() : atPres;
    }


    /**
     * Creates an empty, default loop invariant for the passed loop.
     */
    public LoopInvariantImpl(LoopStatement loop,
                             IProgramMethod pm,
                             KeYJavaType kjt,
	    		     JavaDLTerm selfTerm, 
	    		     Map<LocationVariable,JavaDLTerm> atPres) {
        this(loop, pm, kjt, null, null, null, null, selfTerm, null, null, atPres);
    }


    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Map /*Operator, Operator, JavaDLTerm -> JavaDLTerm*/<JavaDLTerm, JavaDLTerm> getReplaceMap(
            JavaDLTerm selfTerm,
            Map<LocationVariable,JavaDLTerm> atPres,
            Services services) {
        final Map<JavaDLTerm, JavaDLTerm> result = new LinkedHashMap<JavaDLTerm, JavaDLTerm>();
        
        //self
        if(selfTerm != null) {
//            assert selfTerm.sort().extendsTrans(originalSelfTerm.sort()) :
//        	   "instantiating sort " + originalSelfTerm.sort()
//        	   + " with sort " + selfTerm.sort()
//        	   + " which is not a subsort!";
            result.put(originalSelfTerm, selfTerm);
        }
        
        //-parameters and other local variables are always kept up to
        // date by the ProgVarReplaceVisitor

        if(atPres != null) {
            for (Map.Entry<LocationVariable, JavaDLTerm> en : originalAtPres.entrySet()) {
                LocationVariable var = en.getKey();
                JavaDLTerm replace = atPres.get(var);
                JavaDLTerm origReplace = en.getValue();
                if(replace != null && origReplace != null) {
                    assert replace.sort().equals(origReplace.sort());
                    result.put(origReplace, replace);
             }
          }
        }

        return result;
    }
    
    
    private Map<JavaDLTerm,JavaDLTerm> getInverseReplaceMap(JavaDLTerm selfTerm,
                                                Map<LocationVariable,JavaDLTerm> atPres,
                                                Services services) {
       final Map<JavaDLTerm,JavaDLTerm> result = new LinkedHashMap<JavaDLTerm,JavaDLTerm>();
       final Map<JavaDLTerm, JavaDLTerm> replaceMap = getReplaceMap(selfTerm, atPres, services);
       for(Map.Entry<JavaDLTerm, JavaDLTerm> next: replaceMap.entrySet()) {
           result.put(next.getValue(), next.getKey());
       }
       return result;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public LoopStatement getLoop() {
        return loop;
    }

    @Override    
    public JavaDLTerm getInvariant(LocationVariable heap,
                             JavaDLTerm selfTerm,
            		     Map<LocationVariable,JavaDLTerm> atPres,
            		     Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<JavaDLTerm, JavaDLTerm> replaceMap = getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalInvariants.get(heap));
    }
    
    @Override
    public JavaDLTerm getInvariant(JavaDLTerm selfTerm, Map<LocationVariable,JavaDLTerm> atPres, Services services){
        assert (selfTerm == null) == (originalSelfTerm == null);
        LocationVariable baseHeap = services.getTheories().getHeapLDT().getHeap();
        Map<JavaDLTerm, JavaDLTerm> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalModifies.get(baseHeap));
    }
    
    @Override
    public JavaDLTerm getInvariant(Services services) {
        return originalInvariants.get(services.getTheories().getHeapLDT().getHeap());
    }
    
    @Override
    public JavaDLTerm getModifies(LocationVariable heap, JavaDLTerm selfTerm,
            		    Map<LocationVariable,JavaDLTerm> atPres,
            		    Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<JavaDLTerm, JavaDLTerm> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalModifies.get(heap));
    }
    
    @Override
    public JavaDLTerm getModifies(JavaDLTerm selfTerm, Map<LocationVariable,JavaDLTerm> atPres, Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        LocationVariable baseHeap = services.getTheories().getHeapLDT().getHeap();
        Map<JavaDLTerm, JavaDLTerm> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalModifies.get(baseHeap));
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap,
                                                      JavaDLTerm selfTerm,
                                                      Map<LocationVariable, JavaDLTerm> atPres,
                                                      Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<JavaDLTerm, JavaDLTerm> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replaceInfFlowSpec(originalInfFlowSpecs.get(heap));
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap) {
        return originalInfFlowSpecs.get(heap);
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(Services services) {
        LocationVariable baseHeap = services.getTheories().getHeapLDT().getHeap();
        return getInfFlowSpecs(baseHeap);
    }

    @Override
    public JavaDLTerm getVariant(JavaDLTerm selfTerm, 
            		   Map<LocationVariable,JavaDLTerm> atPres,
            		   Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<JavaDLTerm, JavaDLTerm> replaceMap = 
            getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalVariant);
    }

    @Override
    public Map<LocationVariable,JavaDLTerm> getInternalInvariants() {
        return originalInvariants;
    }

    @Override
    public JavaDLTerm getInternalVariant() {
        return originalVariant;
    }

    @Override
    public Map<LocationVariable,JavaDLTerm> getInternalModifies(){
    	return originalModifies;
    }
    
    @Override
    public Map<LocationVariable,
               ImmutableList<InfFlowSpec>> getInternalInfFlowSpec(){
        return originalInfFlowSpecs;
    }
    
    @Override
    public JavaDLTerm getInternalSelfTerm() {
        return originalSelfTerm;
    }

    @Override
    public JavaDLTerm getModifies() {
        return originalModifies.values().iterator().next();
    }
    
    @Override
    public Map<LocationVariable,JavaDLTerm> getInternalAtPres() {
        Map<LocationVariable,JavaDLTerm> result = new LinkedHashMap<LocationVariable,JavaDLTerm>();
//        for(LocationVariable h : originalAtPres.keySet()) {
//          result.put(h, originalAtPres.get(h));
//        }
        result.putAll(originalAtPres);
        return result;
    }

    @Override
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
                                Map<LocationVariable,JavaDLTerm> atPres) {
        return new LoopInvariantImpl(loop, pm, kjt, invariants,
                                     modifies, infFlowSpecs, variant, selfTerm,
                                     localIns, localOuts, atPres);
    }

    @Override
    public LoopInvariant create(LoopStatement loop,
                                Map<LocationVariable,JavaDLTerm> invariants,
                                Map<LocationVariable,JavaDLTerm> modifies,
                                Map<LocationVariable,
                                    ImmutableList<InfFlowSpec>> infFlowSpecs,
                                JavaDLTerm variant,
                                JavaDLTerm selfTerm,
                                ImmutableList<JavaDLTerm> localIns,
                                ImmutableList<JavaDLTerm> localOuts,
                                Map<LocationVariable,JavaDLTerm> atPres) {
        return create(loop, pm, kjt, invariants, modifies, infFlowSpecs,
                      variant, selfTerm, localIns, localOuts, atPres);
    }

    @Override
    public LoopInvariant instantiate(Map<LocationVariable,JavaDLTerm> invariants,
                                     JavaDLTerm variant) {
        return configurate(invariants, originalModifies, originalInfFlowSpecs, variant);
    }

    @Override
    public LoopInvariant configurate(Map<LocationVariable,JavaDLTerm> invariants,
                                     Map<LocationVariable,JavaDLTerm> modifies,
                                     Map<LocationVariable,
                                         ImmutableList<InfFlowSpec>> infFlowSpecs,
                                     JavaDLTerm variant) {
        return create(loop, invariants, modifies, infFlowSpecs, variant,
                      originalSelfTerm, localIns, localOuts, originalAtPres);
    }

    @Override
    public LoopInvariant setLoop(LoopStatement loop) {
        return new LoopInvariantImpl(loop,
                                     pm,
                                     kjt,
                                     originalInvariants,
                                     originalModifies,
                                     originalInfFlowSpecs,
                                     originalVariant,
                                     originalSelfTerm,
                                     localIns,
                                     localOuts,
                                     originalAtPres);
    }

    @Override
    public LoopInvariant setTarget(IProgramMethod newPM) {
        return new LoopInvariantImpl(loop,
                                     newPM,
                                     kjt,
                                     originalInvariants,
                                     originalModifies,
                                     originalInfFlowSpecs,
                                     originalVariant, 
                                     originalSelfTerm,
                                     localIns,
                                     localOuts,
                                     originalAtPres);
    }

    @Override
    public LoopInvariant setInvariant(Map<LocationVariable,JavaDLTerm> invariants, 
            			      JavaDLTerm selfTerm,
            			      Map<LocationVariable,JavaDLTerm> atPres,
            			      Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<JavaDLTerm, JavaDLTerm> inverseReplaceMap 
            = getInverseReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(inverseReplaceMap, services.getTermFactory());
        Map<LocationVariable,JavaDLTerm> newInvariants = new LinkedHashMap<LocationVariable,JavaDLTerm>();
        for(LocationVariable heap : invariants.keySet()) {
           newInvariants.put(heap, or.replace(invariants.get(heap)));
        }
        return new LoopInvariantImpl(loop,
                                     pm,
                                     kjt,
                                     newInvariants,
                                     originalModifies,
                                     originalInfFlowSpecs,
                                     originalVariant,
                                     originalSelfTerm,
                                     localIns,
                                     localOuts,
                                     originalAtPres);
    }
    
    
    @Override
    public void visit(Visitor v) {
        v.performActionOnLoopInvariant(this);
    }
    
    @Override
    public String toString() {
        return "invariants: " 
                + originalInvariants
                + "; modifies: " 
                + originalModifies
                + "; information flow specification: "
                + originalInfFlowSpecs
                + "; variant: "
                + originalVariant
                + "; input parameters: " 
                + localIns
                + "; output parameters: " 
                + localOuts;
    }

    public String getPlainText(Services services, boolean usePrettyPrinting, boolean useUnicodeSymbols) {
       final HeapLDT heapLDT = services.getTheories().getHeapLDT();
       return getPlainText(services, heapLDT.getAllHeaps(), usePrettyPrinting, useUnicodeSymbols);
    }

    @Override
    public String getPlainText(Services services, Iterable<LocationVariable> heapContext, boolean usePrettyPrinting, boolean useUnicodeSymbols) {
       final HeapLDT heapLDT = services.getTheories().getHeapLDT();
       final LocationVariable baseHeap = heapLDT.getHeap();
       
       String mods = "";
       for (LocationVariable h : heapContext) {
           if (originalModifies.get(h) != null) {
               String printMods = LogicPrinter.quickPrintTerm(originalModifies.get(h), services, usePrettyPrinting, useUnicodeSymbols);
               mods = mods
                       + "\n"
                       + "mod"
                       + (h == baseHeap ? "" : "[" + h + "]")
                       + ": "
                       + printMods.trim();
           }
       }
       
       String invariants = "";
       for (LocationVariable h : heapContext) {
           if (originalInvariants.get(h) != null) {
               String printPosts = LogicPrinter.quickPrintTerm(originalInvariants.get(h), services, usePrettyPrinting, useUnicodeSymbols);
               invariants = invariants
                       + "\n"
                       + "invariant"
                       + (h == baseHeap ? "" : "[" + h + "]")
                       + ": "
                       + printPosts.trim();
           }
       }
       
       return invariants
              + (originalVariant != null ? 
                 ";\nvariant: " + LogicPrinter.quickPrintTerm(originalVariant, services, usePrettyPrinting, useUnicodeSymbols).trim() : 
                 ";") +
              mods;
    }


    @Override
    public String getDisplayName() {
	return "Loop Invariant";
    }


    public IProgramMethod getTarget() {
        return this.pm;
    }


    @Override
    public KeYJavaType getKJT() {
	return this.kjt;
    }

    @Override
    public String getName() {
        return "Loop Invariant";
    }

    @Override
    public String getUniqueName() {
        if (pm != null)
            return "Loop Invariant " + getLoop().getStartPosition().getLine() +
                    " " + getTarget().getUniqueName();
        else
            return "Loop Invariant " + getLoop().getStartPosition().getLine() +
                    " " + Math.abs(getLoop().hashCode());
    }

    @Override
    public VisibilityModifier getVisibility() {
	assert false;
	return null;
    }

    @Override
    public boolean hasInfFlowSpec(Services services) {
        return !getInfFlowSpecs(services).isEmpty();
    }

    public LoopInvariant setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        return new LoopInvariantImpl(loop, (IProgramMethod)newPM, newKJT,
                                     originalInvariants, originalModifies,
                                     originalInfFlowSpecs, originalVariant,
                                     originalSelfTerm, localIns, localOuts,
                                     originalAtPres);
    }


    @Override
    public OriginalVariables getOrigVars() {
        Map<LocationVariable, ProgramVariable> atPreVars =
                new LinkedHashMap<LocationVariable, ProgramVariable>();
        for (LocationVariable h: originalAtPres.keySet()) {
            atPreVars.put(h, (ProgramVariable)originalAtPres.get(h).op());
        }
        final ProgramVariable self;
        if(this.originalSelfTerm != null
                && this.originalSelfTerm.op() instanceof ProgramVariable) {
            self = (ProgramVariable)this.originalSelfTerm.op();
        } else if (this.originalSelfTerm != null) {
            self = new LocationVariable(
                    new ProgramElementName(originalSelfTerm.op().toString()), kjt);
        } else {
            self = null;
        }
        return new OriginalVariables(self, null, null, atPreVars,
                                     ImmutableSLList.<ProgramVariable>nil());
    }
}
