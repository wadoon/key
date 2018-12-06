// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.lazyse;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * {@link RuleApp} for the {@link InstantiateAbstractExecutionHoleRule}.
 *
 * @author Dominic Steinhöfel
 */
public class InstantiateAbstractExecutionHoleRuleApp
        extends AbstractBuiltInRuleApp {
    private final AbstractExecutionHoleInstantiation abstractExecutionHole;

    public InstantiateAbstractExecutionHoleRuleApp(
            AbstractExecutionHoleInstantiation abstractExecutionHole) {
        super(InstantiateAbstractExecutionHoleRule.INSTANCE, null);
        this.abstractExecutionHole = abstractExecutionHole;
    }

    @Override
    public boolean complete() {
        return super.complete() && abstractExecutionHole != null;
    }

    public AbstractExecutionHoleInstantiation getAbstractExecutionHoleInstantiation() {
        return abstractExecutionHole;
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return null;
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        /*
         * NOTE (DS, 2018-11-16): As of now, this method should never be called,
         * as the InstantiateLoopHoleInstantiationRule is not supposed to be
         * called automatically.
         */
        return this;
    }

}
