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
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;

public abstract class AbstractBuiltInRuleApp implements IBuiltInRuleApp {

	protected final BuiltInRule builtInRule;

	protected final PosInOccurrence<Term, SequentFormula<Term>> pio;
	protected ImmutableList<PosInOccurrence<Term, SequentFormula<Term>>> ifInsts;

	protected AbstractBuiltInRuleApp(BuiltInRule rule, PosInOccurrence<Term, SequentFormula<Term>> pio,
	                                 ImmutableList<PosInOccurrence<Term, SequentFormula<Term>>> ifInsts) {
        this.builtInRule = rule;
	    this.pio     = pio;
	    this.ifInsts = (ifInsts == null ? ImmutableSLList.<PosInOccurrence<Term, SequentFormula<Term>>>nil() : ifInsts);
	}

	protected AbstractBuiltInRuleApp(BuiltInRule rule, PosInOccurrence<Term, SequentFormula<Term>> pio) {
	    this(rule, pio, null);
	}

	/** HACK: but strategies do not work otherwise in the moment; I need to have a closer look on what is going on there
	 * This restores the behaviour as it was before my previous commit for the moment
	 */
    public void setMutable(ImmutableList<PosInOccurrence<Term, SequentFormula<Term>>> ifInsts) {
        this.ifInsts = ifInsts;
    }

    /**
     * returns the rule of this rule application
     */
    @Override
    public BuiltInRule rule() {
    return builtInRule;
    }

	/**
     * returns the PositionInOccurrence (representing a SequentFormula<Term> and
     * a position in the corresponding formula) of this rule application
     */
    @Override
    public PosInOccurrence<Term, SequentFormula<Term>> posInOccurrence() {
    return pio;
    }

	/** applies the specified rule at the specified position
     * if all schema variables have been instantiated
     * @param goal the Goal where to apply the rule
     * @return list of new created goals
     */
    @Override
    public ImmutableList<Goal> execute(Goal goal) {
    goal.addAppliedRuleApp(this);
    ImmutableList<Goal> result = null;
    try {
        result = builtInRule.apply(goal, this);
    } catch (RuleAbortException rae) {
    }
    if (result == null){
        goal.removeLastAppliedRuleApp();
        goal.node().setAppliedRuleApp(null);
    }
    return result;
    }

    public abstract AbstractBuiltInRuleApp replacePos(PosInOccurrence<Term, SequentFormula<Term>> newPos);

    @Override
    public abstract IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence<Term, SequentFormula<Term>>> ifInsts);

    @Override
    public ImmutableList<PosInOccurrence<Term, SequentFormula<Term>>> ifInsts() {
	return ifInsts;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.IBuiltInRuleApp#tryToInstantiate(de.uka.ilkd.key.proof.Goal)
     */
    @Override
    public abstract AbstractBuiltInRuleApp tryToInstantiate(Goal goal);

    @Override
    public AbstractBuiltInRuleApp forceInstantiate(Goal goal) {
	return tryToInstantiate(goal);
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.IBuiltInRuleApp#isSufficientlyComplete()
     */
    @Override
    public boolean isSufficientlyComplete() {
        return complete();
    }

    @Override
    public List<LocationVariable> getHeapContext() {
      return null;
    }

	/** returns true if all variables are instantiated
     * @return true if all variables are instantiated
     */
    @Override
    public boolean complete() {
    	return true;
    }

	@Override
    public String toString() {
    return "BuiltInRule: " + rule().name() + " at pos " + pio.subTerm();
    }


}
