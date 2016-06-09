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

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Triple;

/**
 * Contracts should only be created through methods of this class
 * @author bruns
 *
 */
public class ContractFactory {

    public static final String SYMB_EXEC_CONTRACT_BASENAME =
            "Symbolic Execution";
    public static final String INFORMATION_FLOW_CONTRACT_BASENAME =
            "Non-interference contract";
    
    private static final String INVALID_ID = "INVALID_ID";
    private static final String UNKNOWN_CONTRACT_IMPLEMENTATION = "unknown contract implementation";
    private static final String CONTRACT_COMBINATION_MARKER = "#";
    private final Services services;
    private final TermBuilder tb;


    public ContractFactory (Services services){
        assert services != null;
        this.services = services;
        this.tb = services.getTermBuilder();
    }

    // PUBLIC INTERFACE

    /**
     * Returns another contract like this one, except that the passed term
     * has been added as a postcondition (regardless of termination case).
     */
    public FunctionalOperationContract
                addPost(FunctionalOperationContract old, JavaDLTerm addedPost, ProgramVariable selfVar,
                        ProgramVariable resultVar, ProgramVariable excVar,
                        ImmutableList<ProgramVariable> paramVars,
                        Map<LocationVariable, LocationVariable> atPreVars) {
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
        addedPost = replaceVariables(addedPost, selfVar, resultVar, excVar, paramVars, atPreVars, 
                                     foci.originalSelfVar, foci.originalResultVar,
                                     foci.originalExcVar, foci.originalParamVars,
                                     foci.originalAtPreVars);

    Map<LocationVariable,JavaDLTerm> newPosts = new LinkedHashMap<LocationVariable,JavaDLTerm>(10);
    for(LocationVariable h : foci.originalPosts.keySet()) {
       if(h == services.getTheories().getHeapLDT().getHeap()) {
          newPosts.put(h, tb.andSC(foci.originalPosts.get(h), addedPost));
       }else{
          newPosts.put(h, foci.originalPosts.get(h));
       }
    }

    //create new contract
    return new FunctionalOperationContractImpl(foci.baseName,
            foci.name,
            foci.kjt,
            foci.pm,
            foci.specifiedIn,
            foci.modality,
            foci.originalPres,
            foci.originalFreePres,
            foci.originalMby,
            newPosts,
            foci.originalFreePosts,
            foci.originalAxioms,
            foci.originalMods,
            foci.originalDeps,
            foci.hasRealModifiesClause,
            foci.originalSelfVar,
            foci.originalParamVars,
            foci.originalResultVar,
            foci.originalExcVar,
            foci.originalAtPreVars,
            foci.globalDefs,
            foci.id,
            foci.toBeSaved,
            foci.transaction, services);
    }

    /** Add the specification contained in InitiallyClause as a postcondition. */
    public FunctionalOperationContract addPost(FunctionalOperationContract old, InitiallyClause ini) {
        final ProgramVariable selfVar = tb.selfVar(ini.getKJT(), true);
        return addPost(old, ini.getClause(selfVar, services), null, null, null, null, null);
    }

    /**
     * Returns another contract like this one, except that the passed term
     * has been added as a precondition.
     */
    public FunctionalOperationContract addPre(FunctionalOperationContract old,
                                              JavaDLTerm addedPre,
                                              ProgramVariable selfVar,
                                              ImmutableList<ProgramVariable> paramVars,
                                              Map<LocationVariable,LocationVariable> atPreVars) {
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci =
                (FunctionalOperationContractImpl) old;
        addedPre =
                replaceVariables(addedPre, selfVar, paramVars, atPreVars,
                                 foci.originalSelfVar, foci.originalParamVars, foci.originalAtPreVars);

      Map<LocationVariable,JavaDLTerm> newPres = new LinkedHashMap<LocationVariable,JavaDLTerm>(10);
      for(LocationVariable h : foci.originalPres.keySet()) {
         if(h == services.getTheories().getHeapLDT().getHeap()) {
            newPres.put(h, tb.and(foci.originalPres.get(h), addedPre));
         }else{
            newPres.put(h, foci.originalPres.get(h));
         }
      }

        //create new contract
        return new FunctionalOperationContractImpl(foci.baseName,
                                                   foci.name,
                                                   foci.kjt,
                                                   foci.pm,
                                                   foci.specifiedIn,
                                                   foci.modality,
                                                   newPres,
                                                   foci.originalFreePres,
                                                   foci.originalMby,
                                                   foci.originalPosts,
                                                   foci.originalFreePosts,
                                                   foci.originalAxioms,
                                                   foci.originalMods,
                                                   foci.originalDeps,
                                                   foci.hasRealModifiesClause,
                                                   foci.originalSelfVar,
                                                   foci.originalParamVars,
                                                   foci.originalResultVar,
                                                   foci.originalExcVar,
                                                   foci.originalAtPreVars,
                                                   foci.globalDefs,
                                                   foci.id,
                                                   foci.toBeSaved,
                                                   foci.originalMods
                                                   .get(services.getTheories().getHeapLDT().getSavedHeap()) != null,
                                                   services);
    }

    /**
     * Add global variable definitions (aka. old clause) to the contract.
     */
    public FunctionalOperationContract addGlobalDefs(FunctionalOperationContract opc,
                                                     JavaDLTerm globalDefs) {
        assert opc instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci =
                (FunctionalOperationContractImpl) opc;
        return new FunctionalOperationContractImpl(foci.baseName, foci.name, foci.kjt, foci.pm,
                                                   foci.specifiedIn, foci.modality,
                                                   foci.originalPres, foci.originalFreePres,
                                                   foci.originalMby, foci.originalPosts,
                                                   foci.originalFreePosts, foci.originalAxioms,
                                                   foci.originalMods, foci.originalDeps,
                                                   foci.hasRealModifiesClause,
                                                   foci.originalSelfVar, foci.originalParamVars,
                                                   foci.originalResultVar, foci.originalExcVar,
                                                   foci.originalAtPreVars, globalDefs, foci.id,
                                                   foci.toBeSaved,foci.transaction, services);
    }

    public DependencyContract dep(KeYJavaType containerType,
                                  IObserverFunction pm,
                                  KeYJavaType specifiedIn,
                                  Map<LocationVariable,JavaDLTerm> requires,
                                  JavaDLTerm measuredBy,
                                  Map<ProgramVariable,JavaDLTerm> accessibles,
                                  ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars,
                                  Map<LocationVariable,? extends ProgramVariable> atPreVars,
                                  JavaDLTerm globalDefs) {
        assert (selfVar == null) == pm.isStatic();
        return dep("JML accessible clause", containerType, pm, specifiedIn,
                   requires, measuredBy, accessibles, selfVar, paramVars, atPreVars, globalDefs);
    }

    public DependencyContract dep(KeYJavaType kjt,
    							  LocationVariable targetHeap,
                                  Triple<IObserverFunction, JavaDLTerm, JavaDLTerm> dep,
                                  ProgramVariable selfVar) {
        final ImmutableList<ProgramVariable> paramVars =
                tb.paramVars(dep.first, false);
        assert (selfVar == null) == dep.first.isStatic();
        Map<LocationVariable,JavaDLTerm> pres = new LinkedHashMap<LocationVariable, JavaDLTerm>();
        pres.put(services.getTheories().getHeapLDT().getHeap(),
                 selfVar == null ? tb.tt() : tb.inv(tb.var(selfVar)));
        Map<ProgramVariable,JavaDLTerm> accessibles = new LinkedHashMap<ProgramVariable, JavaDLTerm>();
        for(LocationVariable heap : HeapContext.getModHeaps(services, false)) {
        	if(heap == targetHeap) {
              accessibles.put(heap, dep.second);
        	}else{
              accessibles.put(heap, tb.allLocs());        		
        	}
        }
        // TODO: insert static invariant??
        return dep(kjt, dep.first, dep.first.getContainerType(), pres, dep.third, accessibles,
                   selfVar, paramVars, null, null);
    }

    public DependencyContract dep(String string,
                                  KeYJavaType containerType,
                                  IObserverFunction pm,
                                  KeYJavaType specifiedIn,
                                  Map<LocationVariable, JavaDLTerm> requires,
                                  JavaDLTerm measuredBy,
                                  Map<ProgramVariable, JavaDLTerm> accessibles,
                                  ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars,
                                  Map<LocationVariable,? extends ProgramVariable> atPreVars,
                                  JavaDLTerm globalDefs) {
        assert (selfVar == null) == pm.isStatic();
        return new DependencyContractImpl(string, null, containerType, pm, specifiedIn,
                                          requires, measuredBy, accessibles,
                                          selfVar, paramVars, atPreVars, globalDefs,
                                          Contract.INVALID_ID);
    }

    public InformationFlowContract createInformationFlowContract(
            KeYJavaType forClass,
            IProgramMethod pm,
            KeYJavaType specifiedIn,
            Modality modality,
            JavaDLTerm requires,
            JavaDLTerm measuredBy,
            JavaDLTerm modifies,
            boolean hasMod,
            ProgramVariableCollection progVars,
            JavaDLTerm accessible,
            ImmutableList<InfFlowSpec> infFlowSpecs,
            boolean toBeSaved) {
        final LocationVariable baseHeap = services.getTheories().getHeapLDT().getHeap();
        final JavaDLTerm atPre = tb.var(progVars.atPreVars.get(baseHeap));
        final JavaDLTerm self = progVars.selfVar != null ? tb.var(progVars.selfVar) : null;
        final ImmutableList<JavaDLTerm> params = tb.var(progVars.paramVars);
        final JavaDLTerm result = progVars.resultVar != null ? tb.var(
                progVars.resultVar) : null;
        final JavaDLTerm exc = progVars.excVar != null ? tb.var(progVars.excVar) : null;
        return new InformationFlowContractImpl(
                INFORMATION_FLOW_CONTRACT_BASENAME, forClass, pm, specifiedIn,
                modality, requires, measuredBy, modifies, hasMod, self, params,
                result, exc, atPre, accessible, infFlowSpecs, toBeSaved);
    }

    @Override
    public boolean equals (Object o){
        if (o instanceof ContractFactory){
            return MiscTools.equalsOrNull(services, ((ContractFactory)o).services);
        } else {
            return false;
        }
    }

    public FunctionalOperationContract func (IProgramMethod pm, InitiallyClause ini) throws SLTranslationException{
            return new JMLSpecFactory(services).initiallyClauseToContract(ini, pm);
    }

    public FunctionalOperationContract func (String baseName,
                                             KeYJavaType kjt,
                                             IProgramMethod pm,
                                             Modality modality,
                                             Map<LocationVariable,JavaDLTerm> pres,
                                             Map<LocationVariable,JavaDLTerm> freePres,
                                             JavaDLTerm mby,
                                             Map<LocationVariable,JavaDLTerm> posts,
                                             Map<LocationVariable,JavaDLTerm> freePosts,
                                             Map<LocationVariable,JavaDLTerm> axioms,
                                             Map<LocationVariable,JavaDLTerm> mods,
                                             Map<ProgramVariable, JavaDLTerm> accs,
                                             Map<LocationVariable,Boolean> hasMod,
                                             ProgramVariable selfVar,
                                             ImmutableList<ProgramVariable> paramVars,
                                             ProgramVariable resultVar,
                                             ProgramVariable excVar,
                                             Map<LocationVariable,LocationVariable> atPreVars,
                                             boolean toBeSaved) {
        return new FunctionalOperationContractImpl(baseName, null, kjt, pm, pm.getContainerType(),
                                                   modality, pres, freePres, mby, posts, freePosts,
                                                   axioms, mods, accs, hasMod, selfVar, paramVars,
                                                   resultVar, excVar, atPreVars, null,
                                                   Contract.INVALID_ID, toBeSaved,
                                                   mods.get(services.getTheories().getHeapLDT()
                                                           .getSavedHeap()) != null, services);
    }

    public FunctionalOperationContract func (String baseName,
                                             IProgramMethod pm,
                                             boolean terminates,
                                             Map<LocationVariable, JavaDLTerm> pres,
                                             Map<LocationVariable, JavaDLTerm> freePres,
                                             JavaDLTerm mby,
                                             Map<LocationVariable, JavaDLTerm> posts,
                                             Map<LocationVariable, JavaDLTerm> freePosts,
                                             Map<LocationVariable, JavaDLTerm> axioms,
                                             Map<LocationVariable, JavaDLTerm> mods,
                                             Map<ProgramVariable, JavaDLTerm> accessibles,
                                             Map<LocationVariable, Boolean> hasMod,
                                             ProgramVariableCollection pv) {
        return func(baseName, pm, terminates ? Modality.DIA : Modality.BOX, pres,
                    freePres, mby, posts, freePosts, axioms,
                    mods, accessibles, hasMod, pv, false, mods.get(
                            services.getTheories().getHeapLDT().getSavedHeap()) != null);
    }


    public FunctionalOperationContract func (String baseName,
                                             IProgramMethod pm,
                                             Modality modality,
                                             Map<LocationVariable, JavaDLTerm> pres,
                                             Map<LocationVariable, JavaDLTerm> freePres,
                                             JavaDLTerm mby,
                                             Map<LocationVariable, JavaDLTerm> posts,
                                             Map<LocationVariable, JavaDLTerm> freePosts,
                                             Map<LocationVariable, JavaDLTerm> axioms,
                                             Map<LocationVariable, JavaDLTerm> mods,
                                             Map<ProgramVariable, JavaDLTerm> accessibles,
                                             Map<LocationVariable, Boolean> hasMod,
                                             ProgramVariableCollection progVars,
                                             boolean toBeSaved, boolean transaction) {
        return new FunctionalOperationContractImpl(baseName, null, pm.getContainerType(), pm,
                                                   pm.getContainerType(), modality, pres, freePres,
                                                   mby, posts, freePosts,
                                                   axioms, mods, accessibles, hasMod,
                                                   progVars.selfVar, progVars.paramVars,
                                                   progVars.resultVar, progVars.excVar,
                                                   progVars.atPreVars, null,
                                                   Contract.INVALID_ID, toBeSaved, transaction, services);
    }

    /**
     * Returns the union of the passed contracts.
     * Probably you want to use SpecificationRepository.combineContracts()
     * instead, which additionally takes care that the combined contract can be
     * loaded later. The resulting contract has id "INVALID_ID".
     */
    public FunctionalOperationContract union(FunctionalOperationContract ... contracts) {
        if (contracts.length == 0) return null;
        if (contracts.length == 1) return contracts[0];
        assert contracts[0] instanceof FunctionalOperationContractImpl :
            UNKNOWN_CONTRACT_IMPLEMENTATION;

        FunctionalOperationContractImpl t = (FunctionalOperationContractImpl) contracts[0];
        FunctionalOperationContract[] others = Arrays.copyOfRange(contracts, 1, contracts.length);
        assert others != null;

        //determine names
        StringBuffer nameSB = new StringBuffer(t.getName());
        for(FunctionalOperationContract other : others) {
            nameSB.append(CONTRACT_COMBINATION_MARKER).append(other.getName());
        }

        for(FunctionalOperationContract contract : others) {
            assert contract.getTarget().equals(t.pm);
        }

        //collect information
        Map<LocationVariable,JavaDLTerm> pres =
                new LinkedHashMap<LocationVariable, JavaDLTerm>(t.originalPres.size());
        for(LocationVariable h : t.originalPres.keySet()) {
           pres.put(h, t.originalPres.get(h));
        }
        JavaDLTerm mby = t.originalMby;
        Map<LocationVariable,Boolean> hasMod = new LinkedHashMap<LocationVariable,Boolean>();
        Map<LocationVariable,JavaDLTerm> posts =
                new LinkedHashMap<LocationVariable, JavaDLTerm>(t.originalPosts.size());
        Map<LocationVariable,JavaDLTerm> freePosts =
                new LinkedHashMap<LocationVariable, JavaDLTerm>(t.originalFreePosts.size());
        for(LocationVariable h : services.getTheories().getHeapLDT().getAllHeaps()) {
           hasMod.put(h, false);
           JavaDLTerm oriPost = t.originalPosts.get(h);
           JavaDLTerm oriFreePost = t.originalFreePosts.get(h);
           if(oriPost != null) {
              posts.put(h,tb.imp(atPreify(t.originalPres.get(h),
                        t.originalAtPreVars),
                   oriPost));
           }
           if(oriFreePost != null) {
               freePosts.put(h, tb.imp(atPreify(t.originalFreePres.get(h), t.originalAtPreVars),
                                       oriFreePost));
            }
        }

        Map<LocationVariable,JavaDLTerm> axioms = new LinkedHashMap<LocationVariable,JavaDLTerm>();
        if(t.originalAxioms != null) { // TODO: what about the others?
            for(LocationVariable h : services.getTheories().getHeapLDT().getAllHeaps()) {
                JavaDLTerm oriAxiom = t.originalAxioms.get(h);
                if(oriAxiom != null) {
                    axioms.put(h,tb.imp(atPreify(t.originalPres.get(h), t.originalAtPreVars),
                                        oriAxiom));
                }
            }
        }
        Map<LocationVariable,JavaDLTerm> mods = t.originalMods;
        Map<ProgramVariable,JavaDLTerm> deps = t.originalDeps;
        Modality moda = t.modality;
        for(FunctionalOperationContract other : others) {
            Modality otherModality = other.getModality();
            if (moda != otherModality) {
                // TODO are there other modalities to appear in contracts?
                // I know that this is extremely ugly, but I don't know how to combine other kinds of modalities.
                if (moda == Modality.BOX) {
                    assert otherModality == Modality.DIA : "unknown modality "+otherModality+" in contract";
                    // do nothing
                } else {
                    assert moda == Modality.DIA: "unknown modality "+moda+" in contract";
                    moda = Modality.BOX;
                }
            }
            JavaDLTerm otherMby = other.hasMby()
            ? other.getMby(t.originalSelfVar,
                    t.originalParamVars,
                    services)
                    : null;
            for(LocationVariable h : services.getTheories().getHeapLDT().getAllHeaps()) {
                JavaDLTerm otherPre = other.getPre(h, t.originalSelfVar,
                        t.originalParamVars,
                        t.originalAtPreVars,
                        services);
                JavaDLTerm otherPost = other.getPost(h, t.originalSelfVar,
                        t.originalParamVars,
                        t.originalResultVar,
                        t.originalExcVar,
                        t.originalAtPreVars,
                        services);
                JavaDLTerm otherFreePost = other.getFreePost(h, t.originalSelfVar,
                                                       t.originalParamVars,
                                                       t.originalResultVar,
                                                       t.originalExcVar,
                                                       t.originalAtPreVars,
                                                       services);
                JavaDLTerm otherAxiom = other.getRepresentsAxiom(h, t.originalSelfVar,
                        t.originalParamVars,
                        t.originalResultVar,
                        t.originalAtPreVars,
                        services);

                if(h == services.getTheories().getHeapLDT().getHeap()) {
                    // bugfix (MU)
                    // if the first or the other contract do not have a
                    // measured-by-clause, assume no clause at all
                    if(mby == null || otherMby == null) {
                        mby = null;
                    } else {
                        mby = tb.ife(otherPre, otherMby, mby);
                    }
                }
                
                // the modifies clause must be computed before the preconditions
                if (hasMod.get(h) || other.hasModifiesClause(h)) {
                    hasMod.put(h, true);
                    JavaDLTerm m1 = mods.get(h);
                    JavaDLTerm m2 = other.getMod(h, t.originalSelfVar,
                            t.originalParamVars,
                            services);
                    Function emptyMod = services.getTheories().getLocSetLDT().getEmpty();
                    if (m1 != null || m2 != null) {
                        JavaDLTerm nm;
                        if (m1 == null) {
                            nm = m2;
                        } else if (m2 == null) {
                            nm = m1;
                        } else if (m1.op().equals(emptyMod) && m2.op().equals(emptyMod)) {
                        	// special case for both contracts being (weakly) pure
                        	// fixes bug #1557
                        	nm = m1;
                        } else {
                            JavaDLTerm ownPre = pres.get(h) != null ? pres.get(h) : tb.tt();
                            nm = tb.intersect(tb.ife(ownPre, m1, tb.allLocs()),
                                    tb.ife(otherPre, m2, tb.allLocs()));
                        }
                        mods.put(h, nm);
                    }
                }
                
                if(otherPre != null) {
                    pres.put(h,pres.get(h) == null ? otherPre : tb.or(pres.get(h), otherPre));
                }
                if(otherPost != null) {
                    final JavaDLTerm oPost = tb.imp(atPreify(otherPre, t.originalAtPreVars), otherPost);
                    posts.put(h, posts.get(h) == null ? oPost : tb.and(posts.get(h), oPost));
                }
                if(otherFreePost != null) {
                    final JavaDLTerm oFreePost = tb.imp(atPreify(otherPre, t.originalAtPreVars), otherFreePost);
                    freePosts.put(h, freePosts.get(h) == null ? oFreePost : tb.and(freePosts.get(h), oFreePost));
                }
                if(otherAxiom != null) {
                    final JavaDLTerm oAxiom = tb.imp(atPreify(otherPre, t.originalAtPreVars), otherAxiom);
                    axioms.put(h, axioms.get(h) == null ? oAxiom : tb.and(axioms.get(h), oAxiom));
                }

                
            }

            for(LocationVariable h : services.getTheories().getHeapLDT().getAllHeaps()) {
                JavaDLTerm a1 = deps.get(h);
                JavaDLTerm a2 = other.getDep(h, false,
                                       t.originalSelfVar,
                                       t.originalParamVars,
                                       t.originalAtPreVars,
                                       services);
                if (a1 != null || a2 != null) {
                    JavaDLTerm na = null;
                    if(a1 == null){
                        na = a2;
                    } else if(a2 == null) {
                        na = a1;
                    }else {
                        na = tb.union(a1, a2);
                    }
                    deps.put(h, na);
                }
                boolean preHeap = t.originalAtPreVars.get(h) != null;
                if (preHeap) {
                    LocationVariable hPre = t.originalAtPreVars.get(h);
                    JavaDLTerm a1Pre = deps.get(hPre);
                    JavaDLTerm a2Pre = other.getDep(hPre, true,
                                              t.originalSelfVar,
                                              t.originalParamVars,
                                              t.originalAtPreVars,
                                              services);
                    if (a1Pre != null || a2Pre != null) {
                        JavaDLTerm naPre = null;
                        if(a1Pre == null){
                            naPre = a2Pre;
                        }else if(a2Pre == null) {
                            naPre = a1Pre;
                        }else{
                            naPre = tb.union(a1Pre, a2Pre);
                        }
                        deps.put(hPre, naPre);
                    }
                }
             }
        }

        /* (*) free preconditions are not joined because no sensible joining operator
         * suggests itself. This is no problem, however, since combined contracts are only used
         * for contract application and free preconditions are not used there.
         * 2015, mu
         */

        return new FunctionalOperationContractImpl(INVALID_ID,
                                                   nameSB.toString(),
                                                   t.kjt,
                                                   t.pm,
                                                   t.specifiedIn,
                                                   moda,
                                                   pres,
                                                   new LinkedHashMap<LocationVariable, JavaDLTerm>(), // (*)
                                                   mby,
                                                   posts,
                                                   freePosts,
                                                   axioms,
                                                   mods,
                                                   deps,
                                                   hasMod,
                                                   t.originalSelfVar,
                                                   t.originalParamVars,
                                                   t.originalResultVar,
                                                   t.originalExcVar,
                                                   t.originalAtPreVars,
                                                   t.globalDefs,
                                                   Contract.INVALID_ID,
                                                   t.toBeSaved,
                                                   t.transaction, services);
    }


    // PRIVATE METHODS

    private static <T> void addToMap(T var, T originalVar,
            Map<T,T> map) {
        if(var != null) {
            map.put(var, originalVar);
        }
    }

    private JavaDLTerm atPreify(JavaDLTerm t, Map<LocationVariable,? extends ProgramVariable> atPreVars) {
        final Map<JavaDLTerm,JavaDLTerm> map = new LinkedHashMap<JavaDLTerm, JavaDLTerm>(atPreVars.size());
        for(LocationVariable h : atPreVars.keySet()) {
          if(atPreVars.get(h) != null) {
            map.put(tb.var(h), tb.var(atPreVars.get(h)));
          }
        }
        return new OpReplacer(map, services.getTermFactory()).replace(t);
    }


    /** replace in original the variables used for self and parameters */
    private JavaDLTerm replaceVariables(JavaDLTerm original, ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars,
                                  Map<LocationVariable,LocationVariable> atPreVars,
                                  ProgramVariable originalSelfVar,
                                  ImmutableList<ProgramVariable> originalParamVars, 
                                  Map<LocationVariable,LocationVariable> originalAtPreVars) {
        return replaceVariables(original,
                                selfVar, null, null, paramVars, atPreVars,
                                originalSelfVar, null, null, originalParamVars, originalAtPreVars);
    }

    /** replace in original the variables used for self, result, exception, heap, and parameters */
    private JavaDLTerm replaceVariables(JavaDLTerm original, ProgramVariable selfVar,
                                  ProgramVariable resultVar, ProgramVariable excVar,
                                  ImmutableList<ProgramVariable> paramVars,
                                  Map<LocationVariable,LocationVariable> atPreVars,
                                  ProgramVariable originalSelfVar,
                                  ProgramVariable originalResultVar,
                                  ProgramVariable originalExcVar,
                                  ImmutableList<ProgramVariable> originalParamVars,
                                  Map<LocationVariable,LocationVariable> originalAtPreVars) {
        Map <Operator, Operator> map = new LinkedHashMap<Operator,Operator>();
        addToMap(selfVar, originalSelfVar, map);
        addToMap(resultVar, originalResultVar, map);
        addToMap(excVar, originalExcVar, map);
        for(LocationVariable h : originalAtPreVars.keySet()) {
           if(atPreVars != null && atPreVars.get(h) != null ) {
             addToMap(atPreVars.get(h), originalAtPreVars.get(h), map);
           }
        }
        if(paramVars != null) {
            Iterator<ProgramVariable> it1 = paramVars.iterator();
            Iterator<ProgramVariable> it2 = originalParamVars.iterator();
            while(it1.hasNext()) {
                assert it2.hasNext();
                map.put(it1.next(), it2.next());
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory());
        original = or.replace(original);
        return original;
    }

    @Override
    public int hashCode() {
        return services == null ? 0 : services.hashCode();
    }


    public static String generateDisplayName(String baseName,
                                             KeYJavaType forClass,
                                             IObserverFunction target,
                                             KeYJavaType specifiedIn,
                                             int myId) {
        return baseName + " " + myId +
                (specifiedIn.equals(forClass)
                  ? ""
                  : " for "
                    + specifiedIn.getProgramType().getFullName());
    }


    public static String generateContractName(String baseName,
                                              KeYJavaType forClass,
                                              IObserverFunction target,
                                              KeYJavaType specifiedIn,
                                              int myId) {
        return generateContractTypeName(baseName, forClass, target, specifiedIn)
               + "." + myId;
    }


    public static String generateContractTypeName(String baseName,
                                                  KeYJavaType forClass,
                                                  IObserverFunction target,
                                                  KeYJavaType specifiedIn) {
        final String methodName = target.name().toString();
        final int startIndexShortName = methodName.indexOf("::") + 2;
        final String methodShortName = methodName.substring(startIndexShortName);
        return forClass.getProgramType().getFullName() + "[" +
               specifiedIn.getProgramType().getFullName() + "::" +
               methodShortName + "(" +
               concadinate(",", target.getParamTypes()) + ")" + "]"
               + "." + baseName;
    }


    private static String concadinate(String delim,
                                      ImmutableArray<KeYJavaType> elems) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < elems.size(); i++) {
            b.append(elems.get(i).getFullName());
            if (i + 1 < elems.size()) {
                b.append(delim);
            }
        }
        return b.toString();
    }
}
