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

package de.tud.cs.se.ds.specstr.rule;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * The {@link RuleApp} for the {@link AnalyzePostCondImpliesMethodEffectsRule}.
 *
 * @author Dominic Steinhoefel
 */
public class AnalyzePostCondImpliesMethodEffectsRuleApp
        extends AbstractBuiltInRuleApp {

    /**
     * Constructor.
     *
     * @param rule
     *            The {@link BuiltInRule} for this app (an
     *            {@link AnalyzePostCondImpliesMethodEffectsRule}).
     * @param pio
     *            The {@link PosInOccurrence} of the rule application.
     */
    protected AnalyzePostCondImpliesMethodEffectsRuleApp(BuiltInRule rule,
            PosInOccurrence pio) {
        super(rule, pio);
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
    public boolean complete() {
        return super.complete();
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        return this;
    }

}
