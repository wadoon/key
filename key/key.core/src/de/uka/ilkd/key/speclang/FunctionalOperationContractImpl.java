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

import static de.uka.ilkd.key.util.Assert.assertEqualSort;
import static de.uka.ilkd.key.util.Assert.assertSubSort;

import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.key_project.common.core.logic.Named;
import org.key_project.common.core.logic.op.ElementaryUpdate;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.SVSubstitute;
import org.key_project.common.core.logic.op.UpdateApplication;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.services.TermServices;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * Standard implementation of the OperationContract interface.
 */
public class FunctionalOperationContractImpl implements FunctionalOperationContract {

    protected final TermBuilder TB; // TODO: Rename into tb
    private final TermServices services;

    final String baseName;
    final String name;
    final KeYJavaType kjt;
    final IProgramMethod pm;
    final KeYJavaType specifiedIn;
    final Modality modality;
    final Map<LocationVariable,JavaDLTerm> originalPres;
    final Map<LocationVariable,JavaDLTerm> originalFreePres;
    final JavaDLTerm originalMby;
    final Map<LocationVariable,JavaDLTerm> originalPosts;
    final Map<LocationVariable,JavaDLTerm> originalFreePosts;
    final Map<LocationVariable,JavaDLTerm> originalAxioms;
    final Map<LocationVariable,JavaDLTerm> originalMods;
    final Map<ProgramVariable, JavaDLTerm> originalDeps;
    final ProgramVariable originalSelfVar;
    final ImmutableList<ProgramVariable> originalParamVars;
    final ProgramVariable originalResultVar;
    final ProgramVariable originalExcVar;
    final Map<LocationVariable,LocationVariable> originalAtPreVars;
    final JavaDLTerm globalDefs;
    final int id;
    final boolean transaction;
    final boolean toBeSaved;

    /**
     * If a method is strictly pure, it has no modifies clause which could
     * be anonymised.
     * @see #hasModifiesClause()
     */
    final Map<LocationVariable,Boolean> hasRealModifiesClause;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------


    /**
     * Creates an operation contract.
     * Using this constructor is discouraged: it may change in the future.
     * Please use the factory methods in {@link de.uka.ilkd.key.speclang.ContractFactory}.
     * @param baseName base name of the contract (does not have to be unique)
    * @param pm the IProgramMethod to which the contract belongs
    * @param modality the modality of the contract
    * @param mby the measured_by clause of the contract
    * @param selfVar the variable used for the receiver object
    * @param paramVars the variables used for the operation parameters
    * @param resultVar the variables used for the operation result
    * @param excVar the variable used for the thrown exception
    * @param globalDefs definitions for the whole contract
    * @param services TODO
    * @param pre the precondition of the contract
    * @param post the postcondition of the contract
    * @param mod the modifies clause of the contract
    * @param heapAtPreVar the variable used for the pre-heap
     */
    FunctionalOperationContractImpl(String baseName,
                                    String name,
                                    KeYJavaType kjt,
                                    IProgramMethod pm,
                                    KeYJavaType specifiedIn,
                                    Modality modality,
                                    Map<LocationVariable,JavaDLTerm> pres,
                                    Map<LocationVariable,JavaDLTerm> freePres,
                                    JavaDLTerm mby,
                                    Map<LocationVariable,JavaDLTerm> posts,
                                    Map<LocationVariable,JavaDLTerm> freePosts,
                                    Map<LocationVariable,JavaDLTerm> axioms,
                                    Map<LocationVariable,JavaDLTerm> mods,
                                    Map<ProgramVariable, JavaDLTerm> accessibles,
                                    Map<LocationVariable,Boolean> hasRealMod,
                                    ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars,
                                    ProgramVariable resultVar,
                                    ProgramVariable excVar,
                                    Map<LocationVariable, LocationVariable> atPreVars,
                                    JavaDLTerm globalDefs,
                                    int id,
                                    boolean toBeSaved,
                                    boolean transaction, TermServices services) {
        assert !(name == null && baseName == null);
        assert kjt != null;
        assert pm != null;
        assert pres != null;
        assert posts != null;
        assert freePres != null;
        assert freePosts != null;
        assert modality != null;
        assert (selfVar == null) == pm.isStatic();
        assert globalDefs == null || globalDefs.sort() == Sort.UPDATE;
        assert paramVars != null;
        assert paramVars.size() >= pm.getParameterDeclarationCount();
        // may be more parameters in specifications (ghost parameters)
        if (resultVar == null){
            assert (pm.isVoid() || pm.isConstructor()) : "resultVar == null for method "+pm;
        } else {
            assert (!pm.isVoid() && !pm.isConstructor()) : "non-null result variable for void method or constructor "+pm+" with return type "+pm.getReturnType();
        }
        assert pm.isModel() || excVar != null;
        assert atPreVars.size() != 0;
        assert services != null;
        this.services = services;
        this.TB = services.getTermBuilder();
        this.baseName               = baseName;
        this.name = name != null
                ? name
                        : ContractFactory.generateContractName(baseName, kjt, pm, specifiedIn, id);
        this.pm          	    = pm;
        this.kjt                    = kjt;
        this.specifiedIn            = specifiedIn;
        this.modality               = modality;
        this.originalPres           = pres;
        this.originalFreePres       = freePres;
        this.originalMby            = mby;
        this.originalPosts          = posts;
        this.originalFreePosts      = freePosts;
        this.originalAxioms         = axioms;
        this.originalMods           = mods;
        this.originalDeps           = accessibles;
        this.hasRealModifiesClause  = hasRealMod;
        this.originalSelfVar        = selfVar;
        this.originalParamVars      = paramVars;
        this.originalResultVar      = resultVar;
        this.originalExcVar         = excVar;
        this.originalAtPreVars      = atPreVars;
        this.globalDefs             = globalDefs;
        this.id                     = id;
        this.transaction            = transaction;
        this.toBeSaved	            = toBeSaved;
    }


    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------


    protected Map<ProgramVariable, ProgramVariable>
                        getReplaceMap(ProgramVariable selfVar,
                                      ImmutableList<ProgramVariable> paramVars,
                                      ProgramVariable resultVar,
                                      ProgramVariable excVar,
                                      Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                                      Services services) {
        final Map<ProgramVariable, ProgramVariable> result =
                new LinkedHashMap<ProgramVariable, ProgramVariable>();

        //self
        if(selfVar != null) {
            assertSubSort(selfVar,originalSelfVar);
            result.put(originalSelfVar, selfVar);
        }

        //parameters
        if(paramVars != null) {
            assert originalParamVars.size() == paramVars.size();
            final Iterator<ProgramVariable> it1 = originalParamVars.iterator();
            final Iterator<ProgramVariable> it2 = paramVars.iterator();
            while(it1.hasNext()) {
                ProgramVariable originalParamVar = it1.next();
                ProgramVariable paramVar         = it2.next();
                // allow contravariant parameter types
                assertSubSort(originalParamVar, paramVar);
                result.put(originalParamVar, paramVar);
            }
        }

        //result
        if(resultVar != null) {
            // workaround to allow covariant return types (bug #1384)
            assertSubSort(resultVar, originalResultVar);
            result.put(originalResultVar, resultVar);
        }

        //exception
        if(excVar != null) {
            assertEqualSort(originalExcVar, excVar);
            result.put(originalExcVar, excVar);
        }

        if(atPreVars != null) {
            final HeapLDT heapLDT = services.getTheories().getHeapLDT();
            for(LocationVariable h : heapLDT.getAllHeaps()) {
                if(atPreVars.get(h) != null) {
                    assertEqualSort(originalAtPreVars.get(h), atPreVars.get(h));
                    result.put(originalAtPreVars.get(h), atPreVars.get(h));
                }
            }
        }

        return result;
    }


    @Deprecated
    protected Map<JavaDLTerm, JavaDLTerm> getReplaceMap(LocationVariable heap, JavaDLTerm heapTerm, JavaDLTerm selfTerm,
                                            ImmutableList<JavaDLTerm> paramTerms, Services services) {
        return getReplaceMap(heap, heapTerm, selfTerm, paramTerms, null, null, null, services);
    }

    @Deprecated
    protected Map<JavaDLTerm, JavaDLTerm> getReplaceMap(LocationVariable heap, JavaDLTerm heapTerm, JavaDLTerm selfTerm,
                                            ImmutableList<JavaDLTerm> paramTerms, JavaDLTerm resultTerm,
                                            JavaDLTerm excTerm, JavaDLTerm atPre, Services services) {
        Map<LocationVariable,JavaDLTerm> heapTerms = new LinkedHashMap<LocationVariable,JavaDLTerm>();
        heapTerms.put(heap, heapTerm);
        Map<LocationVariable,JavaDLTerm> atPres = new LinkedHashMap<LocationVariable,JavaDLTerm>();
        heapTerms.put(heap, atPre);
        return getReplaceMap(heapTerms, selfTerm, paramTerms, resultTerm, excTerm, atPres, services);
    }

    protected Map<JavaDLTerm, JavaDLTerm> getReplaceMap(Map<LocationVariable,JavaDLTerm> heapTerms,
                                            JavaDLTerm selfTerm,
                                            ImmutableList<JavaDLTerm> paramTerms,
                                            JavaDLTerm resultTerm,
                                            JavaDLTerm excTerm,
                                            Map<LocationVariable, JavaDLTerm> atPres,
                                            Services services) {
        final Map<JavaDLTerm,JavaDLTerm> result = new LinkedHashMap<JavaDLTerm,JavaDLTerm>();

        //heaps

        for(LocationVariable heap : heapTerms.keySet()) {
            final JavaDLTerm heapTerm = heapTerms.get(heap);
            assert heapTerm == null || heapTerm.sort().equals(services.getTheories().getHeapLDT()
                    .targetSort());
            result.put(TB.var(heap), heapTerm);
        }

        //self
        if(selfTerm != null) {
            assertSubSort(selfTerm, originalSelfVar);
            result.put(TB.var(originalSelfVar), selfTerm);
        }

        //parameters
        if(paramTerms != null) {
            assert originalParamVars.size() == paramTerms.size();
            final Iterator<ProgramVariable> it1 = originalParamVars.iterator();
            final Iterator<JavaDLTerm> it2 = paramTerms.iterator();
            while(it1.hasNext()) {
                ProgramVariable originalParamVar = it1.next();
                JavaDLTerm paramTerm                   = it2.next();
                // TODO: what does this mean?
                assert paramTerm.sort().extendsTrans(originalParamVar.sort());
                result.put(TB.var(originalParamVar), paramTerm);
            }
        }

        //result
        if(resultTerm != null) {
            assertSubSort(resultTerm, originalResultVar);
            result.put(TB.var(originalResultVar), resultTerm);
        }

        //exception
        if(excTerm != null) {
            assertEqualSort(originalExcVar, excTerm);
            result.put(TB.var(originalExcVar), excTerm);
        }

        if(atPres != null) {
            final HeapLDT heapLDT = services.getTheories().getHeapLDT();
            for(LocationVariable h : heapLDT.getAllHeaps()) {
                if(atPres.get(h) != null) {
                    assertEqualSort(originalAtPreVars.get(h), atPres.get(h));
                    result.put(TB.var(originalAtPreVars.get(h)), atPres.get(h));
                }
            }
        }
        return result;
    }


    /** Make sure ghost parameters appear in the list of parameter variables. */
    private ImmutableList<ProgramVariable> addGhostParams(ImmutableList<ProgramVariable> paramVars) {
        // make sure ghost parameters are present
        ImmutableList<ProgramVariable> ghostParams = ImmutableSLList.<ProgramVariable>nil();
        for (ProgramVariable param: originalParamVars) {
            if (param.isGhost())
                ghostParams = ghostParams.append(param);
        }
        paramVars = paramVars.append(ghostParams);
        return paramVars;
    }

    /** Make sure ghost parameters appear in the list of parameter variables. */
    private ImmutableList<JavaDLTerm> addGhostParamTerms(ImmutableList<JavaDLTerm> paramVars) {
        // make sure ghost parameters are present
        ImmutableList<JavaDLTerm> ghostParams = ImmutableSLList.<JavaDLTerm>nil();
        for (ProgramVariable param: originalParamVars) {
            if (param.isGhost())
                ghostParams = ghostParams.append(TB.var(param));
        }
        paramVars = paramVars.append(ghostParams);
        return paramVars;
    }

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public String getName() {
        return name;
    }


    @Override
    public int id() {
        return id;
    }


    @Override
    public KeYJavaType getKJT() {
        return kjt;
    }


    @Override
    public IProgramMethod getTarget() {
        return pm;
    }


    @Override
    public boolean hasMby() {
        return originalMby != null;
    }


    @Override
    public JavaDLTerm getPre(LocationVariable heap,
                       ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null : "null parameters";
        assert services != null;

        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size() : "number of parameters does not match";

        final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
                                                                               paramVars,
                                                                               null,
                                                                               null,
                                                                               atPreVars,
                                                                               services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalPres.get(heap));
    }


    public JavaDLTerm getPre(List<LocationVariable> heapContext,
                       ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                       Services services) {
        JavaDLTerm result = null;
        for(LocationVariable heap : heapContext) {
            final JavaDLTerm p = getPre(heap, selfVar, paramVars, atPreVars, services);
            if(result == null) {
                result = p;
            }else{
                result = TB.and(result, p);
            }
        }
        return result;
    }


    @Override
    public JavaDLTerm getPre(LocationVariable heap,
                       JavaDLTerm heapTerm,
                       JavaDLTerm selfTerm,
                       ImmutableList<JavaDLTerm> paramTerms,
                       Map<LocationVariable,JavaDLTerm> atPres,
                       Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;

        final Map<LocationVariable,JavaDLTerm> heapTerms = new LinkedHashMap<LocationVariable, JavaDLTerm>();
        heapTerms.put(heap, heapTerm);

	final Map<JavaDLTerm, JavaDLTerm> replaceMap = getReplaceMap(heapTerms,
	                                                 selfTerm,
	                                                 paramTerms,
	                                                 null,
	                                                 null,
	                                                 atPres,
	                                                 services);
	final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
	return or.replace(originalPres.get(heap));
    }


    public JavaDLTerm getPre(List<LocationVariable> heapContext,
                       Map<LocationVariable,JavaDLTerm> heapTerms,
                       JavaDLTerm selfTerm,
                       ImmutableList<JavaDLTerm> paramTerms,
                       Map<LocationVariable,JavaDLTerm> atPres,
                       Services services) {
        JavaDLTerm result = null;
        for(LocationVariable heap : heapContext) {
            final JavaDLTerm p = getPre(heap, heapTerms.get(heap), selfTerm, paramTerms, atPres, services);
            if(p == null) {
                continue;
            }
            if(result == null) {
                result = p;
            }else{
                result = TB.and(result, p);
            }
        }
        return result;
    }


    public JavaDLTerm getFreePre(LocationVariable heap,
                           ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars,
                           Map<LocationVariable,? extends ProgramVariable> atPreVars,
                           Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null : "null parameters";
        assert services != null;

        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size() : "number of parameters does not match";

        final Map<ProgramVariable, ProgramVariable> replaceMap =
                getReplaceMap(selfVar, paramVars, null, null, atPreVars, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalFreePres.get(heap));
    }


    public JavaDLTerm getFreePre(List<LocationVariable> heapContext,
                           ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars,
                           Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                           Services services) {
        JavaDLTerm result = null;
        for(LocationVariable heap : heapContext) {
            final JavaDLTerm p = getFreePre(heap, selfVar, paramVars, atPreVars, services);
            if (result == null) {
                result = p;
            } else if (p != null) {
                result = TB.and(result, p);
            }
        }
        return result;
    }


    public JavaDLTerm getFreePre(LocationVariable heap,
                           JavaDLTerm heapTerm,
                           JavaDLTerm selfTerm,
                           ImmutableList<JavaDLTerm> paramTerms,
                           Map<LocationVariable,JavaDLTerm> atPres,
                           Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;

        final Map<LocationVariable,JavaDLTerm> heapTerms = new LinkedHashMap<LocationVariable, JavaDLTerm>();
        heapTerms.put(heap, heapTerm);

        final Map<JavaDLTerm, JavaDLTerm> replaceMap = getReplaceMap(heapTerms,
                                                         selfTerm,
                                                         paramTerms,
                                                         null,
                                                         null,
                                                         atPres,
                                                         services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalFreePres.get(heap));
    }


    @Override
    public JavaDLTerm getRequires(LocationVariable heap) {
        return originalPres.get(heap);
    }


    @Override
    public JavaDLTerm getEnsures(LocationVariable heap) {
        return originalPosts.get(heap);
    }


    @Override
    public JavaDLTerm getAssignable(LocationVariable heap) {
        return originalMods.get(heap);
    }

    @Override
    public JavaDLTerm getAccessible(ProgramVariable heap) {
        return originalDeps.get(heap);
    }

    @Override
    public JavaDLTerm getMby(ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
	                                                                       paramVars,
	                                                                       null,
	                                                                       null,
	                                                                       null,
	                                                                       services);
	final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
	return or.replace(originalMby);
    }


    @Override
    public JavaDLTerm getMby(Map<LocationVariable,JavaDLTerm> heapTerms, JavaDLTerm selfTerm,
                       ImmutableList<JavaDLTerm> paramTerms, Map<LocationVariable, JavaDLTerm> atPres,
                       Services services) {
        assert heapTerms != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
	final Map<JavaDLTerm, JavaDLTerm> replaceMap = getReplaceMap(heapTerms,
	                                                 selfTerm,
	                                                 paramTerms,
	                                                 null,
	                                                 null,
	                                                 atPres,
	                                                 services);
	final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
	return or.replace(originalMby);
    }

    @Override
    public String getPlainText(Services services) {
        return getText(false, services);
    }

    @Override
    public String getHTMLText(Services services) {
        return getText(true, services);
    }

    private String getText(boolean includeHtmlMarkup, Services services) {
       return getText(pm,
                      originalResultVar,
                      originalSelfVar,
                      originalParamVars,
                      originalExcVar,
                      hasMby(),
                      originalMby,
                      originalMods,
                      hasRealModifiesClause,
                      globalDefs,
                      originalPres,
                      originalFreePres,
                      originalPosts,
                      originalFreePosts,
                      originalAxioms,
                      getModality(),
                      transactionApplicableContract(),
                      includeHtmlMarkup,
                      services,
                      NotationInfo.DEFAULT_PRETTY_SYNTAX,
                      NotationInfo.DEFAULT_UNICODE_ENABLED);
    }
    
    public static String getText(FunctionalOperationContract contract,
                                 ImmutableList<JavaDLTerm> contractParams,
                                 JavaDLTerm resultTerm,
                                 JavaDLTerm contractSelf,
                                 JavaDLTerm excTerm,
                                 LocationVariable baseHeap,
                                 JavaDLTerm baseHeapTerm,
                                 List<LocationVariable> heapContext,
                                 Map<LocationVariable,JavaDLTerm> atPres,
                                 boolean includeHtmlMarkup, 
                                 Services services,
                                 boolean usePrettyPrinting, 
                                 boolean useUnicodeSymbols) {
       Operator originalSelfVar = contractSelf != null ? contractSelf.op() : null;
       Operator originalResultVar = resultTerm != null ? resultTerm.op() : null;
       final TermBuilder tb = services.getTermBuilder();
       
       Map<LocationVariable, JavaDLTerm> heapTerms = new LinkedHashMap<LocationVariable,JavaDLTerm>();
       for(LocationVariable h : heapContext) {
          heapTerms.put(h, tb.var(h));
       }
       
       JavaDLTerm originalMby = contract.hasMby()
             ? contract.getMby(heapTerms,
                   contractSelf,
                   contractParams,
                   atPres,
                   services)
           : null;
       
       Map<LocationVariable,JavaDLTerm> originalMods = new HashMap<LocationVariable, JavaDLTerm>();
       for(LocationVariable heap : heapContext) {
          JavaDLTerm m = contract.getMod(heap, tb.var(heap), contractSelf,contractParams, services);
          originalMods.put(heap, m);
       }
       
       Map<LocationVariable,Boolean> hasRealModifiesClause = new HashMap<LocationVariable, Boolean>();
       for (LocationVariable heap : heapContext) {
          hasRealModifiesClause.put(heap, contract.hasModifiesClause(heap));
       }
       
       JavaDLTerm globalDefs = contract.getGlobalDefs(baseHeap, baseHeapTerm, contractSelf, contractParams, services);
       
       Map<LocationVariable,JavaDLTerm> originalPres = new HashMap<LocationVariable, JavaDLTerm>();
       for (LocationVariable heap : heapContext) {
          JavaDLTerm preTerm = contract.getPre(heap, heapTerms.get(heap), contractSelf, contractParams, atPres, services);
          originalPres.put(heap, preTerm);
       }

       Map<LocationVariable,JavaDLTerm> originalFreePres = new HashMap<LocationVariable, JavaDLTerm>();
       for (LocationVariable heap : heapContext) {
          JavaDLTerm freePreTerm = contract.getFreePre(heap, heapTerms.get(heap), contractSelf,
                                                 contractParams, atPres, services);
          originalFreePres.put(heap, freePreTerm);
       }

       Map<LocationVariable,JavaDLTerm> originalPosts = new HashMap<LocationVariable, JavaDLTerm>();
       for(LocationVariable heap : heapContext) {
          JavaDLTerm p = contract.getPost(heap, heapTerms.get(heap), contractSelf, contractParams,
                                    resultTerm, excTerm, atPres, services);
          originalPosts.put(heap, p);
       }

       Map<LocationVariable,JavaDLTerm> originalFreePosts = new HashMap<LocationVariable, JavaDLTerm>();
       for(LocationVariable heap : heapContext) {
          JavaDLTerm p = contract.getFreePost(heap, heapTerms.get(heap), contractSelf, contractParams,
                                        resultTerm, excTerm, atPres, services);
          originalFreePosts.put(heap, p);
       }

       Map<LocationVariable, ProgramVariable> atPresVars = new HashMap<LocationVariable, ProgramVariable>();
       for (Entry<LocationVariable, JavaDLTerm> entry : atPres.entrySet()) {
          if (entry.getValue() != null) {
             atPresVars.put(entry.getKey(), (ProgramVariable)entry.getValue().op());
          }
          else {
             atPresVars.put(entry.getKey(), null);
          }
       }
       
       Map<LocationVariable,JavaDLTerm> originalAxioms = new HashMap<LocationVariable, JavaDLTerm>();
       for(LocationVariable heap : heapContext) {
          JavaDLTerm p = contract.getRepresentsAxiom(heap, heapTerms.get(heap), contractSelf, contractParams,
                                               resultTerm, excTerm, atPres, services);
          originalAxioms.put(heap, p);
       }
       
       return getText(contract.getTarget(),
                      originalResultVar,
                      originalSelfVar,
                      contractParams,
                      (ProgramVariable)excTerm.op(),
                      contract.hasMby(),
                      originalMby,
                      originalMods,
                      hasRealModifiesClause,
                      globalDefs,
                      originalPres,
                      originalFreePres,
                      originalPosts,
                      originalFreePosts,
                      originalAxioms,
                      contract.getModality(),
                      contract.transactionApplicableContract(),
                      includeHtmlMarkup,
                      services,
                      usePrettyPrinting,
                      useUnicodeSymbols);
    }

    private static String getText(IProgramMethod pm, 
                                  Operator originalResultVar, 
                                  Operator originalSelfVar, 
                                  ImmutableList<? extends SVSubstitute> originalParamVars,
                                  ProgramVariable originalExcVar,
                                  boolean hasMby,
                                  JavaDLTerm originalMby,
                                  Map<LocationVariable,JavaDLTerm> originalMods,
                                  Map<LocationVariable,Boolean> hasRealModifiesClause,
                                  JavaDLTerm globalDefs,
                                  Map<LocationVariable,JavaDLTerm> originalPres,
                                  Map<LocationVariable,JavaDLTerm> originalFreePres,
                                  Map<LocationVariable,JavaDLTerm> originalPosts,
                                  Map<LocationVariable,JavaDLTerm> originalFreePosts,
                                  Map<LocationVariable,JavaDLTerm> originalAxioms,
                                  Modality modality,
                                  boolean transaction,
                                  boolean includeHtmlMarkup, 
                                  Services services,
                                  boolean usePrettyPrinting, 
                                  boolean useUnicodeSymbols) {
        final HeapLDT heapLDT = services.getTheories().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();
        final LocationVariable baseHeap = heapLDT.getHeap();
        final StringBuffer sig = new StringBuffer();
        if (originalResultVar != null) {
            sig.append(originalResultVar);
            sig.append(" = ");
        }
        else if (pm.isConstructor()) {
            sig.append(originalSelfVar);
            sig.append(" = new ");
        }
        if (!pm.isStatic() && !pm.isConstructor()) {
            sig.append(originalSelfVar);
            sig.append(".");
        }
        sig.append(pm.getName());
        sig.append("(");
        for (SVSubstitute subst : originalParamVars) {
           if (subst instanceof Named) {
              Named named = (Named)subst;
              sig.append(named.name()).append(", ");
           }
           else if (subst instanceof JavaDLTerm) {
              sig.append(LogicPrinter.quickPrintTerm((JavaDLTerm)subst, services, usePrettyPrinting, useUnicodeSymbols).trim()).append(", ");
           }
           else {
              sig.append(subst).append(", ");
           }
        }
        if (!originalParamVars.isEmpty()) {
            sig.setLength(sig.length() - 2);
        }
        sig.append(")");
        if(!pm.isModel()) {
            sig.append(" catch(");
            sig.append(originalExcVar);
            sig.append(")");
        }

        final String mby = hasMby ? LogicPrinter.quickPrintTerm(originalMby, services, usePrettyPrinting, useUnicodeSymbols) : null;

        String mods = "";
        for (LocationVariable h : heapLDT.getAllHeaps()) {
            if (originalMods.get(h) != null) {
                String printMods = LogicPrinter.quickPrintTerm(originalMods.get(h), services, usePrettyPrinting, useUnicodeSymbols);
                mods = mods
                        + (includeHtmlMarkup ? "<br><b>" : "\n")
                        + "mod"
                        + (h == baseHeap ? "" : "[" + h + "]")
                        + (includeHtmlMarkup ? "</b> " : ": ")
                        + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printMods, false) : printMods.trim());
                if (!hasRealModifiesClause.get(h)) {
                    mods = mods +
                            (includeHtmlMarkup ? "<b>" : "") +
                            ", creates no new objects" +
                            (includeHtmlMarkup ? "</b>" : "");
                }
            }
        }

        String globalUpdates = "";
        if (globalDefs!=null){
            final String printUpdates = LogicPrinter.quickPrintTerm(globalDefs, services, usePrettyPrinting, useUnicodeSymbols);
            globalUpdates = (includeHtmlMarkup? "<br><b>": "\n")
                    + "defs" + (includeHtmlMarkup? "</b> " : ": ")
                    + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printUpdates,false) : printUpdates.trim());
        }

        String pres = "";
        for (LocationVariable h : heapLDT.getAllHeaps()) {
            if (originalPres.get(h) != null) {
                String printPres = LogicPrinter.quickPrintTerm(originalPres.get(h), services, usePrettyPrinting, useUnicodeSymbols);
                pres = pres
                        + (includeHtmlMarkup ? "<br><b>" : "\n")
                        + "pre"
                        + (h == baseHeap ? "" : "[" + h + "]")
                        + (includeHtmlMarkup ? "</b> " : ": ")
                        + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printPres, false) : printPres.trim());
            }
        }

        String freePres = "";
        for (LocationVariable h : heapLDT.getAllHeaps()) {
            JavaDLTerm freePre = originalFreePres.get(h);
            if (freePre != null && !freePre.equals(tb.tt())) {
                String printFreePres = LogicPrinter.quickPrintTerm(freePre, services,
                                                                   usePrettyPrinting, useUnicodeSymbols);
                freePres = freePres
                        + (includeHtmlMarkup ? "<br><b>" : "\n")
                        + "free pre"
                        + (h == baseHeap ? "" : "[" + h + "]")
                        + (includeHtmlMarkup ? "</b> " : ": ")
                        + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printFreePres, false) : printFreePres.trim());
            }
        }

        String posts = "";
        for (LocationVariable h : heapLDT.getAllHeaps()) {
            if (originalPosts.get(h) != null) {
                String printPosts = LogicPrinter.quickPrintTerm(originalPosts.get(h), services, usePrettyPrinting, useUnicodeSymbols);
                posts = posts
                        + (includeHtmlMarkup ? "<br><b>" : "\n")
                        + "post"
                        + (h == baseHeap ? "" : "[" + h + "]")
                        + (includeHtmlMarkup ? "</b> " : ": ")
                        + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printPosts, false) : printPosts.trim());
            }
        }

        String freePosts = "";
        for (LocationVariable h : heapLDT.getAllHeaps()) {
            JavaDLTerm freePost = originalFreePosts.get(h);
            if (freePost != null && !freePost.equals(tb.tt())) {
                String printFreePosts = LogicPrinter.quickPrintTerm(freePost, services,
                                                                    usePrettyPrinting, useUnicodeSymbols);
                freePosts = freePosts
                        + (includeHtmlMarkup ? "<br><b>" : "\n")
                        + "free post"
                        + (h == baseHeap ? "" : "[" + h + "]")
                        + (includeHtmlMarkup ? "</b> " : ": ")
                        + (includeHtmlMarkup ?
                                LogicPrinter.escapeHTML(printFreePosts, false) : printFreePosts.trim());
            }
        }

        String axioms = "";
        if (originalAxioms != null) {
            for(LocationVariable h : heapLDT.getAllHeaps()) {
                if(originalAxioms.get(h) != null) {
                    String printAxioms = LogicPrinter.quickPrintTerm(originalAxioms.get(h), services, usePrettyPrinting, useUnicodeSymbols);
                    posts = posts
                            + (includeHtmlMarkup ? "<br><b>" : "\n")
                            + "axiom"
                            + (h == baseHeap ? "" : "[" + h + "]")
                            + (includeHtmlMarkup ? "</b> " : ": ")
                            + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printAxioms, false) : printAxioms.trim());
                }
            }
        }

        if (includeHtmlMarkup) {
            return "<html>"
                    + "<i>"
                    + LogicPrinter.escapeHTML(sig.toString(), false)
                    + "</i>"
                    + globalUpdates
                    + pres
                    + freePres
                    + posts
                    + freePosts
                    + axioms
                    + mods
                    + (hasMby ? "<br><b>measured-by</b> "+ LogicPrinter.escapeHTML(mby, false) : "")
                    + "<br><b>termination</b> "
                    + modality
                    + (transaction ? "<br><b>transaction applicable</b>" : "") +
                    "</html>";

        }
        else {
            return sig.toString()
                    + globalUpdates
                    + pres
                    + freePres
                    + posts
                    + freePosts
                    + axioms
                    + mods
                    + (hasMby ? "\nmeasured-by: "+ mby : "")
                    + "\ntermination: "
                    + modality
                    + (transaction ? "\ntransaction applicable:" : "");
        }
    }


    @Override
    public boolean toBeSaved() {
        return toBeSaved;
    }


    @Override
    public String proofToString(Services services) {
        assert toBeSaved;
        final StringBuffer sb = new StringBuffer();
        final HeapLDT heapLDT = services.getTheories().getHeapLDT();
        final LocationVariable baseHeap = heapLDT.getHeap();
        sb.append(baseName).append(" {\n");

        //print var decls
        sb.append("  \\programVariables {\n");
        if(originalSelfVar != null) {
            sb.append("    ").append(originalSelfVar.proofToString());
        }
        for(ProgramVariable originalParamVar : originalParamVars) {
            sb.append("    ").append(originalParamVar.proofToString());
        }
        if(originalResultVar != null) {
            sb.append("    ").append(originalResultVar.proofToString());
        }
        sb.append("    ").append(originalExcVar.proofToString());
        sb.append("    ").append(originalAtPreVars.get(baseHeap).proofToString());
        sb.append("  }\n");

        //prepare Java program
        final Expression[] args
        = new ProgramVariable[originalParamVars.size()];
        int i = 0;
        for(ProgramVariable arg : originalParamVars) {
            args[i++] = arg;
        }
        final MethodReference mr
        = new MethodReference(new ImmutableArray<Expression>(args),
                pm.getProgramElementName(),
                originalSelfVar);
        final Statement callStatement;
        if(originalResultVar == null) {
            callStatement = mr;
        } else {
            callStatement = new CopyAssignment(originalResultVar, mr);
        }
        final CatchAllStatement cas
        = new CatchAllStatement(new StatementBlock(callStatement),
                (LocationVariable)originalExcVar);
        final StatementBlock sblock = new StatementBlock(cas);
        final JavaBlock jb = JavaBlock.createJavaBlock(sblock);

        //print contract term
        final JavaDLTerm update
        = TB.tf().createTerm(
                ElementaryUpdate.getInstance(originalAtPreVars.get(baseHeap)),
                TB.getBaseHeap());
        final JavaDLTerm modalityTerm
        = TB.tf().createTerm(modality,
                new JavaDLTerm[]{originalPosts.get(baseHeap)},
                new ImmutableArray<QuantifiableVariable>(),
                jb);
        final JavaDLTerm updateTerm
        = TB.tf().createTerm(UpdateApplication.UPDATE_APPLICATION,
                update,
                modalityTerm);
        final JavaDLTerm contractTerm
        = TB.tf().createTerm(Junctor.IMP, originalPres.get(baseHeap), updateTerm);
        final LogicPrinter lp = new LogicPrinter(new ProgramPrinter(),
                new NotationInfo(),
                null);
        try {
            lp.printTerm(contractTerm);
        } catch(IOException e) {
            throw new RuntimeException(e);
        }
        sb.append(lp.toString());

        //print modifies
        lp.reset();
        try {
            lp.printTerm(originalMods.get(baseHeap));
        } catch(IOException e) {
            throw new RuntimeException(e);
        }
        sb.append("  \\modifies ").append(lp.toString());

        sb.append("};\n");
        return sb.toString();
    }


    @Override
    public Modality getModality() {
        return modality;
    }

    @Override
    public JavaDLTerm getPost(LocationVariable heap,
                        ProgramVariable selfVar,
                        ImmutableList<ProgramVariable> paramVars,
                        ProgramVariable resultVar,
                        ProgramVariable excVar,
                        Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                        Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert pm.isModel() || excVar != null;
        assert atPreVars.size() != 0;
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
                paramVars,
                resultVar,
                excVar,
                atPreVars,
                services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalPosts.get(heap));
    }

    public JavaDLTerm getPost(List<LocationVariable> heapContext,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar,
            ProgramVariable excVar,
            Map<LocationVariable,? extends ProgramVariable> atPreVars,
            Services services) {
        JavaDLTerm result = null;
        for(LocationVariable heap : heapContext) {
            final JavaDLTerm p = getPost(heap, selfVar, paramVars, resultVar, excVar, atPreVars, services);
            if(result == null) {
                result = p;
            }else{
                result = TB.and(result, p);
            }
        }
        return result;

    }

    @Override
    public JavaDLTerm getPost(LocationVariable heap,
                        JavaDLTerm heapTerm,
                        JavaDLTerm selfTerm,
                        ImmutableList<JavaDLTerm> paramTerms,
                        JavaDLTerm resultTerm,
                        JavaDLTerm excTerm,
                        Map<LocationVariable, JavaDLTerm> atPres,
                        Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert (resultTerm == null) == (originalResultVar == null);
        assert pm.isModel() || excTerm != null;
        assert atPres.size() != 0;
        assert services != null;
        final Map<LocationVariable,JavaDLTerm> heapTerms = new LinkedHashMap<LocationVariable, JavaDLTerm>();
        heapTerms.put(heap, heapTerm);

        final Map<JavaDLTerm, JavaDLTerm> replaceMap = getReplaceMap(heapTerms,
                                                         selfTerm,
                                                         paramTerms,
                                                         resultTerm,
                                                         excTerm,
                                                         atPres,
                                                         services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalPosts.get(heap));
    }

    public JavaDLTerm getPost(List<LocationVariable> heapContext,
                        Map<LocationVariable,JavaDLTerm> heapTerms,
                        JavaDLTerm selfTerm,
                        ImmutableList<JavaDLTerm> paramTerms,
                        JavaDLTerm resultTerm,
                        JavaDLTerm excTerm,
                        Map<LocationVariable, JavaDLTerm> atPres,
                        Services services) {
        JavaDLTerm result = null;
        for(LocationVariable heap : heapContext) {
            final JavaDLTerm p = getPost(heap, heapTerms.get(heap), selfTerm, paramTerms, resultTerm, excTerm, atPres, services);
            if(p == null) {
                continue;
            }
            if(result == null) {
                result = p;
            }else{
                result = TB.and(result, p);
            }
        }
        return result;
    }

    public JavaDLTerm getFreePost(LocationVariable heap,
                            ProgramVariable selfVar,
                            ImmutableList<ProgramVariable> paramVars,
                            ProgramVariable resultVar,
                            ProgramVariable excVar,
                            Map<LocationVariable,? extends ProgramVariable> atPreVars,
                            Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert pm.isModel() || excVar != null;
        assert atPreVars.size() != 0;
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replaceMap =
                getReplaceMap(selfVar, paramVars, resultVar, excVar, atPreVars, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalFreePosts.get(heap));
    }

    public JavaDLTerm getFreePost(LocationVariable heap,
                            JavaDLTerm heapTerm,
                            JavaDLTerm selfTerm,
                            ImmutableList<JavaDLTerm> paramTerms,
                            JavaDLTerm resultTerm,
                            JavaDLTerm excTerm,
                            Map<LocationVariable,JavaDLTerm> atPres,
                            Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert (resultTerm == null) == (originalResultVar == null);
        assert pm.isModel() || excTerm != null;
        assert atPres.size() != 0;
        assert services != null;
        final Map<LocationVariable,JavaDLTerm> heapTerms = new LinkedHashMap<LocationVariable, JavaDLTerm>();
        heapTerms.put(heap, heapTerm);

        final Map<JavaDLTerm, JavaDLTerm> replaceMap = getReplaceMap(heapTerms,
                                                         selfTerm,
                                                         paramTerms,
                                                         resultTerm,
                                                         excTerm,
                                                         atPres,
                                                         services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalFreePosts.get(heap));
    }

    public JavaDLTerm getFreePost(List<LocationVariable> heapContext,
                            Map<LocationVariable,JavaDLTerm> heapTerms,
                            JavaDLTerm selfTerm,
                            ImmutableList<JavaDLTerm> paramTerms,
                            JavaDLTerm resultTerm,
                            JavaDLTerm excTerm,
                            Map<LocationVariable,JavaDLTerm> atPres,
                            Services services) {
        JavaDLTerm result = null;
        for(LocationVariable heap : heapContext) {
            final JavaDLTerm p = getFreePost(heap, heapTerms.get(heap), selfTerm, paramTerms,
                                       resultTerm, excTerm, atPres, services);
            if(p == null) {
                continue;
            }
            if(result == null) {
                result = p;
            }else{
                result = TB.and(result, p);
            }
        }
        return result;
    };

    @Override
    public JavaDLTerm getRepresentsAxiom(LocationVariable heap,
                                   ProgramVariable selfVar,
                                   ImmutableList<ProgramVariable> paramVars,
                                   ProgramVariable resultVar,
                                   Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                                   Services services) {
        assert (selfVar == null) == (originalSelfVar == null):
            "Illegal instantiation:" + (originalSelfVar == null?
                            "this is a static contract, instantiated with self variable '"+selfVar+"'"
                            : "this is an instance contract, instantiated without a self variable");
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert atPreVars.size() != 0;
        assert services != null;
        if(originalAxioms == null) {
            return null;
        }
        final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
                paramVars,
                resultVar,
                null,
                atPreVars,
                services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalAxioms.get(heap));
    }

    @Override
    public JavaDLTerm getRepresentsAxiom(LocationVariable heap, 
                                   JavaDLTerm heapTerm, 
                                   JavaDLTerm selfTerm, 
                                   ImmutableList<JavaDLTerm> paramTerms, 
                                   JavaDLTerm resultTerm, 
                                   JavaDLTerm excTerm,
                                   Map<LocationVariable, JavaDLTerm> atPres, 
                                   Services services) {
       assert heapTerm != null;
       assert (selfTerm == null) == (originalSelfVar == null);
       assert paramTerms != null;
       paramTerms = addGhostParamTerms(paramTerms);
       assert paramTerms.size() == originalParamVars.size();
       assert (resultTerm == null) == (originalResultVar == null);
       assert pm.isModel() || excTerm != null;
       assert atPres.size() != 0;
       assert services != null;
       final Map<LocationVariable,JavaDLTerm> heapTerms = new LinkedHashMap<LocationVariable, JavaDLTerm>();
       heapTerms.put(heap, heapTerm);

       final Map<JavaDLTerm, JavaDLTerm> replaceMap = getReplaceMap(heapTerms,
               selfTerm,
               paramTerms,
               resultTerm,
               excTerm,
               atPres,
               services);
       final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
       return or.replace(originalAxioms.get(heap));
    }

    public boolean isReadOnlyContract(Services services) {
        return originalMods.get(services.getTheories().getHeapLDT().getHeap()).op() ==
                services.getTheories().getLocSetLDT().getEmpty();
    }

    public JavaDLTerm getAnyMod(JavaDLTerm mod, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar,
                                                                               paramVars,
                                                                               null,
                                                                               null,
                                                                               null,
                                                                               services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(mod);
    }

    @Override
    public JavaDLTerm getMod(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Services services) {
        return getAnyMod(this.originalMods.get(heap), selfVar, paramVars, services);
    }

    private JavaDLTerm getAnyMod(LocationVariable heap, JavaDLTerm mod, JavaDLTerm heapTerm,
            JavaDLTerm selfTerm,
            ImmutableList<JavaDLTerm> paramTerms,
            Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;

        final Map<LocationVariable,JavaDLTerm> heapTerms = new LinkedHashMap<LocationVariable, JavaDLTerm>();
        heapTerms.put(heap, heapTerm);

        final Map<JavaDLTerm, JavaDLTerm> replaceMap = getReplaceMap(heapTerms,
                                                         selfTerm,
                                                         paramTerms,
                                                         null,
                                                         null,
                                                         null,
                                                         services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(mod);
    }

    @Override
    public boolean hasModifiesClause(LocationVariable heap) {
        Boolean result = this.hasRealModifiesClause.get(heap);
        if(result == null) {
            return false;
        }
        return result;
    }

    @Override
    public JavaDLTerm getMod(LocationVariable heap, JavaDLTerm heapTerm,
                       JavaDLTerm selfTerm,
                       ImmutableList<JavaDLTerm> paramTerms,
                       Services services) {
        return getAnyMod(heap, this.originalMods.get(heap), heapTerm, selfTerm, paramTerms, services);
    }

    @Override
    public JavaDLTerm getDep(LocationVariable heap, boolean atPre,
                       ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable,? extends ProgramVariable> atPreVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        Map<SVSubstitute, SVSubstitute> map = new LinkedHashMap<SVSubstitute, SVSubstitute>();
        if (originalSelfVar != null) {
            map.put(originalSelfVar, selfVar);
        }
        for(ProgramVariable originalParamVar : originalParamVars) {
            map.put(originalParamVar, paramVars.head());
            paramVars = paramVars.tail();
        }
        if(atPreVars != null && originalAtPreVars != null) {
            for(LocationVariable h : services.getTheories().getHeapLDT().getAllHeaps()) {
                ProgramVariable originalAtPreVar = originalAtPreVars.get(h);
                if(atPreVars.get(h) != null && originalAtPreVar != null) {
                    map.put(TB.var(atPre ? h : originalAtPreVar), TB.var(atPreVars.get(h)));
                }
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory());
        return or.replace(originalDeps.get(atPre ? originalAtPreVars.get(heap) : heap));
    }


    @Override
    public JavaDLTerm getDep(LocationVariable heap, boolean atPre,
                       JavaDLTerm heapTerm, JavaDLTerm selfTerm,
                       ImmutableList<JavaDLTerm> paramTerms,
                       Map<LocationVariable, JavaDLTerm> atPres,
                       Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        Map<SVSubstitute, SVSubstitute> map = new LinkedHashMap<SVSubstitute, SVSubstitute>();
        map.put(TB.var(heap), heapTerm);
        if (originalSelfVar != null) {
            map.put(TB.var(originalSelfVar), selfTerm);
        }
        for(ProgramVariable originalParamVar : originalParamVars) {
            map.put(TB.var(originalParamVar), paramTerms.head());
            paramTerms = paramTerms.tail();
        }
        if(atPres != null && originalAtPreVars != null) {
            for(LocationVariable h : services.getTheories().getHeapLDT().getAllHeaps()) {
                ProgramVariable originalAtPreVar = originalAtPreVars.get(h);
                if(originalAtPreVar != null && atPres.get(h) != null) {
                    map.put(TB.var(originalAtPreVar), atPres.get(h));
                }
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory());
        return or.replace(originalDeps.get(atPre ? originalAtPreVars.get(heap) : heap));
    }

    @Override
    public JavaDLTerm getGlobalDefs() {
        return this.globalDefs;
    }

    @Override
    public JavaDLTerm getGlobalDefs(LocationVariable heap, JavaDLTerm heapTerm, JavaDLTerm selfTerm,
                              ImmutableList<JavaDLTerm> paramTerms, Services services) {
        if (globalDefs==null) return null;
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        final Map<JavaDLTerm, JavaDLTerm> replaceMap = getReplaceMap(heap, heapTerm,
                selfTerm,
                paramTerms,
                services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(globalDefs);
    }

    @Override
    public String toString() {
        final LocationVariable heap = ((Services)services).getTheories().getHeapLDT().getHeap();
        return
                (globalDefs == null? "": "defs: "+ globalDefs +"; ")
                + "pre: "
                + originalPres
                + (originalFreePres.get(heap) != null
                    && !originalFreePres.get(heap).equalsModRenaming(TB.tt()) ?
                            "free pre: " + originalFreePres : "")
                + "; mby: "
                + originalMby
                + "; post: "
                + originalPosts
                + (originalFreePosts.get(heap) != null
                    && !originalFreePosts.get(heap).equalsModRenaming(TB.tt()) ?
                            "free post: " + originalFreePosts : "")
                + "; mods: "
                + originalMods
                + "; hasMod: "
                + hasRealModifiesClause
                + (originalAxioms != null && originalAxioms.size() > 0 ?  ("; axioms: " + originalAxioms) : "")
                + "; termination: "
                + getModality()
                + "; transaction: "
                + transactionApplicableContract();
    }


    @Override
    public final ContractPO createProofObl(InitConfig initConfig) {
        return (ContractPO)createProofObl(initConfig, this);
    }


    @Override
    public ProofOblInput getProofObl(Services services) {
        return services.getSpecificationRepository().getPO(this);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract) {
        return new FunctionalOperationContractPO(initConfig,
                (FunctionalOperationContract) contract);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract, boolean addSymbolicExecutionLabel) {
        return new FunctionalOperationContractPO(initConfig,
                (FunctionalOperationContract) contract, false, addSymbolicExecutionLabel);
    }


    @Override
    public String getDisplayName() {
        return ContractFactory.generateDisplayName(baseName, kjt, pm, specifiedIn, id);
    }


    @Override
    public VisibilityModifier getVisibility() {
        assert false; // this is currently not applicable for contracts
        return null;
    }

    public boolean transactionApplicableContract() {
        return transaction;
    }

    @Override
    public FunctionalOperationContract setID(int newId) {
        return new FunctionalOperationContractImpl(baseName,
                                                   null,
                                                   kjt,
                                                   pm,
                                                   specifiedIn,
                                                   modality,
                                                   originalPres,
                                                   originalFreePres,
                                                   originalMby,
                                                   originalPosts,
                                                   originalFreePosts,
                                                   originalAxioms,
                                                   originalMods,
                                                   originalDeps,
                                                   hasRealModifiesClause,
                                                   originalSelfVar,
                                                   originalParamVars,
                                                   originalResultVar,
                                                   originalExcVar,
                                                   originalAtPreVars,
                                                   globalDefs,
                                                   newId,
                                                   toBeSaved,
                                                   transaction, 
                                                   services);
    }


    @Override
    public Contract setTarget(KeYJavaType newKJT,
            IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        return new FunctionalOperationContractImpl(baseName,
                                                   null,
                                                   newKJT,
                                                   (IProgramMethod) newPM,
                                                   specifiedIn,
                                                   modality,
                                                   originalPres,
                                                   originalFreePres,
                                                   originalMby,
                                                   originalPosts,
                                                   originalFreePosts,
                                                   originalAxioms,
                                                   originalMods,
                                                   originalDeps,
                                                   hasRealModifiesClause,
                                                   originalSelfVar,
                                                   originalParamVars,
                                                   originalResultVar,
                                                   originalExcVar,
                                                   originalAtPreVars,
                                                   globalDefs,
                                                   id,
                                                   toBeSaved && newKJT.equals(kjt),
                                                   transaction, services);
    }


    @Override
    public String getTypeName() {
        return ContractFactory.generateContractTypeName(baseName, kjt, pm, specifiedIn);
    }


   @Override
   public boolean hasSelfVar() {
      return originalSelfVar != null;
   }

    @Override
    public String getBaseName() {
        return baseName;
    }


    @Override
    public JavaDLTerm getPre() {
        assert originalPres.values().size() == 1
               : "information flow extension not compatible with multi-heap setting";
        return originalPres.values().iterator().next();
    }


    @Override
    public JavaDLTerm getPost() {
        assert originalPosts.values().size() == 1
               : "information flow extension not compatible with multi-heap setting";
        return originalPosts.values().iterator().next();
    }


    @Override
    public JavaDLTerm getMod() {
        return originalMods.values().iterator().next();
    }


    @Override
    public JavaDLTerm getMby() {
        return originalMby;
    }


    @Override
    public JavaDLTerm getSelf() {
        if (originalSelfVar == null){
            assert pm.isStatic() : "missing self variable in non-static method contract";
            return null;
        }
        return TB.var(originalSelfVar);
    }

    @Override
    public boolean hasResultVar() {
       return originalResultVar != null;
    }


    @Override
    public ImmutableList<JavaDLTerm> getParams() {
        if (originalParamVars == null) {
            return null;
        }
        return TB.var(originalParamVars);
    }


    @Override
    public JavaDLTerm getResult() {
        if (originalResultVar == null) {
            return null;
        }
        return TB.var(originalResultVar);
    }


    @Override
    public JavaDLTerm getExc() {
        if (originalExcVar == null) {
            return null;
        }
        return TB.var(originalExcVar);
    }

    public KeYJavaType getSpecifiedIn() {
	    return specifiedIn;
    }

    @Override
    public OriginalVariables getOrigVars() {
        Map<LocationVariable, ProgramVariable> atPreVars =
                new LinkedHashMap<LocationVariable, ProgramVariable>();
        for (LocationVariable h: originalAtPreVars.keySet()) {
            atPreVars.put(h, originalAtPreVars.get(h));
        }
        return new OriginalVariables(originalSelfVar, originalResultVar,
                                     originalExcVar, atPreVars, originalParamVars);
    }
}