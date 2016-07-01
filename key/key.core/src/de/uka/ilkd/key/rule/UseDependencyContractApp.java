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

import java.util.List;

import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaDLTermServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.HeapContext;

public class UseDependencyContractApp extends AbstractContractRuleApp {

    private final PosInOccurrence<Term> step;
    private List<LocationVariable> heapContext;
	
	public UseDependencyContractApp(BuiltInRule builtInRule, PosInOccurrence<Term> pio) {
	    this(builtInRule, pio, null, null);
    }

	public UseDependencyContractApp(BuiltInRule builtInRule, PosInOccurrence<Term> pio,
			Contract instantiation, PosInOccurrence<Term> step) {
	    this(builtInRule, pio, ImmutableSLList.<PosInOccurrence<Term>>nil(), instantiation, step);
    }
	
    public UseDependencyContractApp(BuiltInRule rule,
                                    PosInOccurrence<Term> pio, ImmutableList<PosInOccurrence<Term>> ifInsts,
                                    Contract contract, PosInOccurrence<Term> step) {
	    super(rule, pio, ifInsts, contract);
	    this.step = step;

    }

    public UseDependencyContractApp replacePos(PosInOccurrence<Term> newPos) {
	    return new UseDependencyContractApp(rule(), newPos, ifInsts, instantiation, step);
    }

    public boolean isSufficientlyComplete() {
    	return pio != null && instantiation != null && !ifInsts.isEmpty();    	
    }
    
    public boolean complete() {
    	return super.complete() && step != null;
    }

    private UseDependencyContractApp computeStep(Sequent seq, Services services) {
        assert this.step == null;
        final List<PosInOccurrence<Term>> steps =
            UseDependencyContractRule.
            getSteps(this.getHeapContext(), this.posInOccurrence(), seq, services);                
        PosInOccurrence<Term> l_step =
            UseDependencyContractRule.findStepInIfInsts(steps, this, services);
        assert l_step != null;/* 
				: "The strategy failed to properly "
				+ "instantiate the base heap!\n"
				+ "at: " + app.posInOccurrence().subTerm() + "\n"
				+ "ifInsts: " + app.ifInsts() + "\n"
				+ "steps: " + steps;*/
        return setStep(l_step);
    }


    public PosInOccurrence<Term> step(Sequent seq, JavaDLTermServices services) {
        return step;
    }

    public UseDependencyContractApp setStep(PosInOccurrence<Term> p_step) {
        assert this.step == null;
        return new UseDependencyContractApp(rule(), 
                posInOccurrence(), ifInsts(), instantiation, p_step);
    }

	@Override
    public UseDependencyContractApp setContract(Contract contract) {
	    return new UseDependencyContractApp(builtInRule, posInOccurrence(), ifInsts, 
	    		contract, step);
    }
	
    public UseDependencyContractRule rule() {
    	return (UseDependencyContractRule) super.rule();
    }

    public UseDependencyContractApp tryToInstantiate(Goal goal) {
        if(heapContext == null){
            heapContext = HeapContext.getModHeaps(goal.getServices(), false);
        }
        if (complete()) {
            return this;
        }
        UseDependencyContractApp app = this;

        final Services services = goal.getServices();

        app = tryToInstantiateContract(services);		

        if (!app.complete() && app.isSufficientlyComplete()) {
            app = app.computeStep(goal.sequent(), services);
        }
        return app;
    }
    
    public UseDependencyContractApp tryToInstantiateContract(final Services services) {
        final Term focus = posInOccurrence().subTerm();
        if (! (focus.op() instanceof IObserverFunction))
            // TODO: find more appropriate exception
            throw new RuntimeException("Dependency contract rule is not applicable to term "+focus);
        final IObserverFunction target = (IObserverFunction) focus.op();

        final Term selfTerm;
        final KeYJavaType kjt;

        if (target.isStatic()) {
            selfTerm = null;
            kjt = target.getContainerType();
        } else {
            if(getHeapContext() == null) {
                heapContext = HeapContext.getModHeaps(services, false);
            }
            selfTerm = focus.sub(target.getStateCount() * target.getHeapCount(services));
            kjt = services.getProgramServices().getJavaInfo().getKeYJavaType(
                    selfTerm.sort());
        }
        ImmutableSet<Contract> contracts = UseDependencyContractRule.getApplicableContracts(
                services, kjt, target);

        if (contracts.size() > 0) {
            UseDependencyContractApp r = setContract(contracts.iterator().next());
            if(r.getHeapContext() == null) {
                r.heapContext = HeapContext.getModHeaps(services, false);
            }
            return r;
        }
        return this;
    }

    @Override
    public List<LocationVariable> getHeapContext() {
        return heapContext;
    }

    @Override
    public IObserverFunction getObserverFunction(Services services) {
        final Operator op = posInOccurrence().subTerm().op();
        return (IObserverFunction) (op instanceof IObserverFunction ? op : null); 
    }

    
    
    @Override
    public UseDependencyContractApp setIfInsts(ImmutableList<PosInOccurrence<Term>> ifInsts) {
        setMutable(ifInsts);
        return this;
        //return new UseDependencyContractApp(builtInRule, pio, ifInsts, instantiation, step);
    }


	
}