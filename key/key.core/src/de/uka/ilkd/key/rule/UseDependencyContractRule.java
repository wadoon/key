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

package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.LogicVariable;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.services.TermServices;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyContract;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.util.Pair;


public final class UseDependencyContractRule implements BuiltInRule {

    public static final UseDependencyContractRule INSTANCE
                                            = new UseDependencyContractRule();

    private static final Name NAME = new Name("Use Dependency Contract");



    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    private UseDependencyContractRule() {
    }



    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    private static List<JavaDLTerm> getEqualityDefs(JavaDLTerm term, Sequent seq) {
	final List<JavaDLTerm> result = new LinkedList<JavaDLTerm>();
	for(SequentFormula cf : seq.antecedent()) {
	    final JavaDLTerm formula = cf.formula();
	    if(formula.op() instanceof Equality
	       && formula.sub(1).equals(term)) {
		result.add(formula.sub(0));
	    }
	}
	return result;
    }


    private static List<Pair<JavaDLTerm,PosInOccurrence>> getEqualityDefsAndPos(JavaDLTerm term,
	    						    	   Sequent seq){
	final List<Pair<JavaDLTerm,PosInOccurrence>> result
		= new LinkedList<Pair<JavaDLTerm,PosInOccurrence>>();
	for(SequentFormula cf : seq.antecedent()) {
	    final JavaDLTerm formula = cf.formula();
	    if(formula.op() instanceof Equality
	       && formula.sub(1).equals(term)) {
		final PosInOccurrence pos
			= new PosInOccurrence(cf, PosInTerm.getTopLevel(), true);
		result.add(new Pair<JavaDLTerm,PosInOccurrence>(formula.sub(0), pos));
	    }
	}
	return result;
    }


    private ImmutableSet<JavaDLTerm> addEqualDefs(ImmutableSet<JavaDLTerm> terms, Goal g) {
	ImmutableSet<JavaDLTerm> result = terms;
	for(SequentFormula cf : g.sequent().antecedent()) {
	    final JavaDLTerm formula = cf.formula();
	    if(formula.op() instanceof Equality
	        && terms.contains(formula.sub(1))) {
		result = result.add(formula.sub(0));
	    }
	}
	return result;
    }


    private boolean hasRawSteps(JavaDLTerm heapTerm, Sequent seq, Services services) {
	final HeapLDT heapLDT = services.getTheories().getHeapLDT();
	final Operator op = heapTerm.op();
	assert heapTerm.sort().equals(heapLDT.targetSort());
	if(op == heapLDT.getStore()
	   || op == heapLDT.getCreate()
           || op == heapLDT.getAnon()
	   || op == heapLDT.getMemset()) {
	   return true;
	} else if(op.arity() == 0) {
	    final List<JavaDLTerm> defs = getEqualityDefs(heapTerm, seq);
	    for(JavaDLTerm def : defs) {
		if(hasRawSteps(def, seq, services)) {
		    return true;
		}
	    }
	    return false;
	} else {
	    return false;
	}
    }


    private static void getRawSteps(JavaDLTerm heapTerm,
	    		     Sequent seq,
	    		     Services services,
	    		     List<JavaDLTerm> result) {
	final HeapLDT heapLDT = services.getTheories().getHeapLDT();
	final Operator op = heapTerm.op();
	assert heapTerm.sort().equals(heapLDT.targetSort());
	if(op == heapLDT.getStore()
           || op == heapLDT.getCreate()
  	   || op == heapLDT.getAnon()
           || op == heapLDT.getMemset()) {
	    final JavaDLTerm h = heapTerm.sub(0);
	    result.add(h);
	    getRawSteps(h, seq, services, result);
	} else if(op.arity() == 0) {
	    final List<JavaDLTerm> defs = getEqualityDefs(heapTerm, seq);
	    for(JavaDLTerm def : defs) {
		getRawSteps(def, seq, services, result);
	    }
	}
    }


    private static PosInOccurrence getFreshLocsStep(PosInOccurrence heapPos,
	    				     Sequent seq,
	    				     Services services) {
	final HeapLDT heapLDT = services.getTheories().getHeapLDT();
	final LocSetLDT locSetLDT = services.getTheories().getLocSetLDT();
	final JavaDLTerm heapTerm = heapPos.subTerm();
	final Operator op = heapTerm.op();
	assert heapTerm.sort().equals(heapLDT.targetSort());
	if(heapTerm.op() == heapLDT.getAnon()
	   && heapTerm.sub(1).op().equals(locSetLDT.getEmpty())) {
	    return heapPos;
	} else if(op.arity() == 0) {
	    final List<Pair<JavaDLTerm,PosInOccurrence>> defs
	    	= getEqualityDefsAndPos(heapTerm, seq);
	    for(Pair<JavaDLTerm,PosInOccurrence> def : defs) {
		final PosInOccurrence defHeapPos = def.second.down(0);
		assert defHeapPos.subTerm().equals(def.first);
		final PosInOccurrence pos
			= getFreshLocsStep(defHeapPos, seq, services);
		if(pos != null) {
		    return pos;
		}
	    }
	    return null;
	} else {
	    return null;
	}
    }


    private static Pair<JavaDLTerm,ImmutableList<PosInOccurrence>>
    		 getChangedLocsForStep(JavaDLTerm heapTerm,
	                       	       JavaDLTerm stepHeap,
	                       	       Sequent seq,
	                       	       Services services) {
	final HeapLDT heapLDT = services.getTheories().getHeapLDT();
	final Operator op = heapTerm.op();
	assert heapTerm.sort().equals(heapLDT.targetSort());
	final TermBuilder TB = services.getTermBuilder();
	if(heapTerm.equals(stepHeap)) {
	    return new Pair<JavaDLTerm,ImmutableList<PosInOccurrence>>(
		    		TB.empty(),
		    		ImmutableSLList.<PosInOccurrence>nil());
	} else if(op == heapLDT.getStore()) {
	    final JavaDLTerm h = heapTerm.sub(0);
	    final JavaDLTerm o = heapTerm.sub(1);
	    final JavaDLTerm f = heapTerm.sub(2);
	    final JavaDLTerm locs = TB.singleton(o, f);
	    final Pair<JavaDLTerm,ImmutableList<PosInOccurrence>> furtherLocs
	    	= getChangedLocsForStep(h, stepHeap, seq, services);
	    return new Pair<JavaDLTerm,ImmutableList<PosInOccurrence>>(
		    	    TB.union(locs, furtherLocs.first),
		    	    furtherLocs.second);
	} else if(op == heapLDT.getCreate()) {
	    final JavaDLTerm h = heapTerm.sub(0);
	    final Pair<JavaDLTerm,ImmutableList<PosInOccurrence>> furtherLocs
	    	= getChangedLocsForStep(h, stepHeap, seq, services);
	    return furtherLocs;
	} else if(op == heapLDT.getAnon() || op == heapLDT.getMemset()) {
	    final JavaDLTerm h = heapTerm.sub(0);
	    final JavaDLTerm s = heapTerm.sub(1);
	    final Pair<JavaDLTerm,ImmutableList<PosInOccurrence>> furtherLocs
	    	= getChangedLocsForStep(h, stepHeap, seq, services);
	    return new Pair<JavaDLTerm,ImmutableList<PosInOccurrence>>(
		    	    TB.union(s, furtherLocs.first),
	                    furtherLocs.second);
	} else if(op.arity() == 0) {
	    final List<Pair<JavaDLTerm,PosInOccurrence>> defs
	    	= getEqualityDefsAndPos(heapTerm, seq);
	    for(Pair<JavaDLTerm,PosInOccurrence> def : defs) {
		final Pair<JavaDLTerm,ImmutableList<PosInOccurrence>> furtherLocs
		    = getChangedLocsForStep(def.first, stepHeap, seq, services);
		if(furtherLocs != null) {
		    return new Pair<JavaDLTerm,ImmutableList<PosInOccurrence>>(
				furtherLocs.first,
			        furtherLocs.second.prepend(def.second));
		}
	    }
	}
	return null;
    }


    public static boolean isBaseOcc(JavaDLTerm focus, JavaDLTerm candidate) {
	if(!candidate.op().equals(focus.op())) {
	    return false;
	}
	for(int i = 1, n = candidate.arity(); i < n; i++) {
	    if(!(candidate.sub(i).equals(focus.sub(i))
		 || candidate.sub(i).op() instanceof LogicVariable)) {
		return false;
	    }
	}
	return true;
    }


    private static void collectBaseOccsHelper(JavaDLTerm focus,
	    			       PosInOccurrence pos,
    				       Map<JavaDLTerm, PosInOccurrence> result) {
	final JavaDLTerm candidate = pos.subTerm();
	if(isBaseOcc(focus, candidate)) {
	    result.put(candidate.sub(0), pos);
        }
	for(int i = 0, n = candidate.arity(); i < n; i++) {
	    collectBaseOccsHelper(focus, pos.down(i), result);
	}
    }


    private static Map<JavaDLTerm, PosInOccurrence> collectBaseOccs(JavaDLTerm focus,
	    					       Sequent seq) {
	assert focus.op() instanceof IObserverFunction;
	final Map<JavaDLTerm, PosInOccurrence> result
		= new LinkedHashMap<JavaDLTerm, PosInOccurrence>();
	for(SequentFormula cf : seq.antecedent()) {
	    final PosInOccurrence pos
	    	= new PosInOccurrence(cf, PosInTerm.getTopLevel(), true);
	    collectBaseOccsHelper(focus, pos, result);
	}
	for(SequentFormula cf : seq.succedent()) {
	    final PosInOccurrence pos
	    	= new PosInOccurrence(cf, PosInTerm.getTopLevel(), false);
	    collectBaseOccsHelper(focus, pos, result);
	}
	return result;
    }


    public static List<PosInOccurrence> getSteps(
    		              List<LocationVariable> heapContext,
                          PosInOccurrence pos,
	    				  Sequent seq,
	    				  Services services) {
	final JavaDLTerm focus = pos.subTerm();
	assert focus.op() instanceof IObserverFunction;

	final List<PosInOccurrence> result
		= new LinkedList<PosInOccurrence>();

	//special treatment for anon(h, empty, h')
	final PosInOccurrence freshLocsStep
		= getFreshLocsStep(pos.down(0), seq, services);
	if(freshLocsStep != null) {
	    result.add(freshLocsStep);
	    return result;
	}

	//get raw steps
	final List<JavaDLTerm> rawSteps = new LinkedList<JavaDLTerm>();
	int index = 0;
	final int stateCount = ((IObserverFunction)focus.op()).getStateCount();
	final int numHeaps = ((IObserverFunction)focus.op()).getHeapCount(services);
	while(index < stateCount*numHeaps) {
	  getRawSteps(focus.sub(index++), seq, services, rawSteps);
	  if(((IObserverFunction)focus.op()).getStateCount() == 2) {
		  getRawSteps(focus.sub(index++), seq, services, rawSteps);
	  }
	  if(rawSteps.size() > 0) {
	      //get base occs
	      final Map<JavaDLTerm, PosInOccurrence> baseOccs
	    	  = collectBaseOccs(focus, seq);

  	      //filter steps
	      for(JavaDLTerm rawStep : rawSteps) {
		    final PosInOccurrence step = baseOccs.get(rawStep);
		    if(step != null) {
		       result.add(step);
	 	    }
	      }
	  }
	}

	return result;
    }



    public static PosInOccurrence findStepInIfInsts(
	    		List<PosInOccurrence> steps,
	    		UseDependencyContractApp app,
	    		TermServices services) {
    	for(PosInOccurrence pio : app.ifInsts()) {
    		if(steps.contains(pio)) {
    			return pio;
    		}
    	}
    	return null;
    }


    /**
     * Returns the dependency contracts which are applicable for the passed
     * target.
     */
    public static ImmutableSet<Contract> getApplicableContracts(
	    					Services services,
                                                KeYJavaType kjt,
                                                IObserverFunction target) {
        ImmutableSet<Contract> result
        	= services.getSpecificationRepository().getContracts(kjt,
        							     target);
        for(Contract contract : result) {
            if(!(contract instanceof DependencyContract)) {
        	result = result.remove(contract);
            }
        }
        return result;
    }



    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public boolean isApplicable(Goal goal,
                                PosInOccurrence pio) {
	if(pio == null) {
	    return false;
	}

	//top level symbol must be observer
	final JavaDLTerm focus = pio.subTerm();
	if(!(focus.op() instanceof IObserverFunction)) {
	    return false;
	}

	//there must not be free variables in the focus term
	if(!focus.freeVars().isEmpty()) {
	    return false;
	}

	// abort if inside of transformer
        if (Transformer.inTransformer(pio)) {
            return false;
        }

	//heap term of observer must be store-term (or anon, create,
	//memset, ...)
	final Services services = goal.proof().getServices();
	final IObserverFunction target = (IObserverFunction) focus.op();
	//final List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
	boolean hasRawSteps = false;
	for(int i = 0; i<target.getHeapCount(services) * target.getStateCount(); i++) {
	  if(hasRawSteps(focus.sub(i), goal.sequent(), services)) {
        hasRawSteps = true;		  
	    break;
	  }
	}
	if(!hasRawSteps) {
	    return false;
	}
	//there must be contracts for the observer
	final KeYJavaType kjt
		= target.isStatic()
		  ? target.getContainerType()
	          : services.getProgramServices().getJavaInfo().getKeYJavaType(
	                  focus.sub(target.getHeapCount(services)*target.getStateCount()).sort());
	assert kjt != null : "could not determine receiver type for " + focus;
	if(kjt.getSort() instanceof NullSort) {
	    return false;
	}
        final ImmutableSet<Contract> contracts
        	= getApplicableContracts(services, kjt, target);
        if(contracts.isEmpty()) {
            return false;
        }

        //applying a contract here must not create circular dependencies
        //between proofs
        return goal.proof()
                   .mgt()
                   .isContractApplicable(contracts.iterator().next());
    }


    @Override
    public ImmutableList<Goal> apply(Goal goal,
	    			     Services services,
	    			     RuleApp ruleApp) {
	//collect information
	final LocSetLDT locSetLDT = services.getTheories().getLocSetLDT();
	final PosInOccurrence pio = ruleApp.posInOccurrence();
        final JavaDLTerm focus = pio.subTerm();
        final IObserverFunction target = (IObserverFunction) focus.op();
        final List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
        final TermBuilder TB = services.getTermBuilder();
        
        final JavaDLTerm selfTerm;
        if (target.isStatic()) {
            selfTerm = null;
        } else {
            selfTerm = focus.sub(target.getHeapCount(services)*target.getStateCount());
        }

        ImmutableList<JavaDLTerm> paramTerms = ImmutableSLList.<JavaDLTerm>nil();
        for(int i = target.getHeapCount(services)*target.getStateCount() + (target.isStatic() ? 0 : 1); i < focus.arity(); i++) {
            paramTerms = paramTerms.append(focus.sub(i));
        }

        //configure contract
        final DependencyContract contract =
        		(DependencyContract)((UseDependencyContractApp) ruleApp).getInstantiation();
        assert contract != null;

        //get step
        final PosInOccurrence step =
                ((UseDependencyContractApp)ruleApp).step(goal.sequent(), services);

        final boolean twoState = target.getStateCount() == 2;
        final int obsHeapCount = target.getHeapCount(services);
        Map<LocationVariable,JavaDLTerm> atPres = twoState ? new LinkedHashMap<LocationVariable, JavaDLTerm>() : null;
        Map<LocationVariable,JavaDLTerm> heapTerms = new LinkedHashMap<LocationVariable, JavaDLTerm>();
        int i=0;
        for(LocationVariable heap : heaps) {
        	if(i >= obsHeapCount) {
        		break;
        	}
            heapTerms.put(heap, step.subTerm().sub(2*i));
            if(twoState) {
            	atPres.put(heap, step.subTerm().sub(2*i+1));
            }
            i++;
        }
        final JavaDLTerm mby = contract.hasMby()
           	 ? contract.getMby(heapTerms, selfTerm, paramTerms, atPres, services) : null;

        assert !step.subTerm().equals(focus);
        
        JavaDLTerm freePre = !target.isStatic() ? TB.not(TB.equals(selfTerm, TB.NULL())) : null;
        JavaDLTerm disjoint = null;
        JavaDLTerm pre = null;
        final JavaDLTerm[] subs = focus.subs().toArray(new JavaDLTerm[focus.arity()]);
        int heapExprIndex = 0;
        boolean useful = false;
        ImmutableList<PosInOccurrence> ifInsts = ImmutableSLList.<PosInOccurrence>nil();
        int hc = 0;
        for(LocationVariable heap : heaps) {
          if(hc >= obsHeapCount) {
        	  break;
          }
          for(boolean atPre : twoState ? new boolean[] { false, true } : new boolean[] { false } ) {
            //get changed locs and used equalities
            final JavaDLTerm subStep = step.subTerm().sub(heapExprIndex);
            final Pair<JavaDLTerm,ImmutableList<PosInOccurrence>> changedLocs  = getChangedLocsForStep(focus.sub(heapExprIndex),
                        subStep,
                        goal.sequent(),
                        services);

            assert changedLocs != null;
            //store insts 
            ifInsts = ifInsts.append(changedLocs.second.prepend(step));
            if(!target.isStatic()) {
                final JavaDLTerm cr = TB.created(subStep, selfTerm);
                if(freePre == null) {
                	freePre = cr;
                }else{
                    freePre = TB.and(freePre, cr);
                }
            }
            final JavaDLTerm wf = TB.and(TB.wellFormed(subStep), TB.wellFormed(focus.sub(heapExprIndex)));
            if(freePre == null) {
            	freePre = wf;
            }else{
                freePre = TB.and(freePre, wf);
            }
            i = 0;
    	    for(JavaDLTerm paramTerm : paramTerms) {
    	    	assert freePre != null;
    	        freePre = TB.and(freePre, TB.reachableValue(subStep,
    					       		paramTerm,
    					       		target.getParamType(i++)));
    	    }
    	    final JavaDLTerm dep = contract.getDep(heap, atPre, subStep, selfTerm, paramTerms, atPres, services);
    	    final JavaDLTerm ds = TB.disjoint(changedLocs.first, dep);
    	    if(disjoint == null) {
               disjoint = ds;
            } else {
    	       disjoint = TB.and(disjoint, ds);
            }
            // check if helpful
            if(!useful && !changedLocs.first.op().equals(locSetLDT.getEmpty())) {
                final ImmutableSet<JavaDLTerm> changed
                	= addEqualDefs(TB.unionToSet(
                				      changedLocs.first),
                				      goal);
                if(!changed.contains(dep)) {
            	  useful = true;
                }
            }else{
            	useful = true;
            }
            if(!atPre) {
              final JavaDLTerm p = contract.getPre(heap, subStep, selfTerm, paramTerms, atPres, services);
              if(p != null) {
                if(pre == null) {
            	  pre = p;
                }else{
                  pre = TB.and(pre, p);
                }
              }
              subs[heapExprIndex] = subStep;
            }
            heapExprIndex++;
          }
          hc++;
        }

        //store insts in rule app
        ruleApp = ((IBuiltInRuleApp) ruleApp).setIfInsts(ifInsts);

        //create justification
        final RuleJustificationBySpec just
                = new RuleJustificationBySpec(contract);
        final ComplexRuleJustificationBySpec cjust
                = (ComplexRuleJustificationBySpec)
                    goal.proof().getInitConfig().getJustifInfo().getJustification(this);
        cjust.add(ruleApp, just);

        if(!useful) {
        	return goal.split(1);        	
        }

        //prepare cut formula
  	    final ContractPO po
		    = services.getSpecificationRepository()
			    .getContractPOForProof(goal.proof());
	    final JavaDLTerm mbyOk;
	    if(po != null && /* po.getMbyAtPre() != null && */ mby != null) {
//	        mbyOk = TB.and(TB.leq(TB.zero(services), mby, services),
//		           TB.lt(mby, po.getMbyAtPre(), services));
//                mbyOk = TB.prec(mby, po.getMbyAtPre(), services);
            mbyOk = TB.measuredByCheck(mby);
	    } else {
	       mbyOk = TB.tt();
	    }
        final JavaDLTerm cutFormula = TB.and(freePre, pre, disjoint, mbyOk);


        //create "Post" branch
        final ImmutableList<Goal> result = goal.split(1);
        final JavaDLTerm termWithBaseHeap = TB.func(target, subs);
        final JavaDLTerm implication =
                TB.imp(cutFormula, TB.equals(focus, termWithBaseHeap));
        result.head().addFormula(new SequentFormula(implication), true, false);

        return result;
    }


    @Override
    public Name name() {
        return NAME;
    }


    @Override
    public String displayName() {
        return NAME.toString();
    }


    @Override
    public String toString() {
        return displayName();
    }

    public UseDependencyContractApp createApp(PosInOccurrence pos) {
       return createApp(pos, null);
    }
    
    @Override
    public UseDependencyContractApp createApp(PosInOccurrence pos, TermServices services) {
		return new UseDependencyContractApp(this, pos);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isApplicableOnSubTerms() {
       return true;
    }
}
