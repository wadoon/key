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

package de.tud.cs.se.ds.specstr.strategy;

import de.tud.cs.se.ds.specstr.rule.AbstractAnalysisRule;
import de.tud.cs.se.ds.specstr.rule.AnalyzeInvImpliesLoopEffectsRule;
import de.tud.cs.se.ds.specstr.rule.AnalyzePostCondImpliesMethodEffectsRule;
import de.tud.cs.se.ds.specstr.rule.FactAnalysisRule;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.rulefilter.SetRuleFilter;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.feature.ConditionalFeature;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;

/**
 * A {@link SymbolicExecutionStrategy} with the {@link AbstractAnalysisRule}s.
 *
 * @author Dominic Steinhoefel
 */
public class StrengthAnalysisStrategy extends SymbolicExecutionStrategy {
    /**
     * The {@link Name} of this strategy; will be saved in proo file headers.
     */
    public static final Name NAME = new Name("Strength Analysis Strategy");

    /**
     * Constructor.
     *
     * @param proof
     *            The {@link Proof} this {@link Strategy} should be used for.
     * @param sp
     *            The {@link StrategyProperties} settings.
     */
    protected StrengthAnalysisStrategy(Proof proof, StrategyProperties sp) {
        super(proof, sp);
    }

    /**
     * The {@link StrategyFactory} to create strategies of type
     * {@link StrengthAnalysisStrategy}.
     *
     * @author Dominic Steinhoefel
     */
    public static class Factory extends SymbolicExecutionStrategy.Factory {
        @Override
        public Strategy create(Proof proof, StrategyProperties sp) {
            return new StrengthAnalysisStrategy(proof, sp);
        }

        @Override
        public Name name() {
            return NAME;
        }
    }

    @Override
    protected Feature setupGlobalF(Feature dispatcher) {
        Feature globalF = super.setupGlobalF(dispatcher);

        globalF = add(globalF, strengthAnalysisFeature(inftyConst()));

        return globalF;
    }

    private static Feature strengthAnalysisFeature(Feature cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(AnalyzeInvImpliesLoopEffectsRule.INSTANCE);
        filter.addRuleToSet(AnalyzePostCondImpliesMethodEffectsRule.INSTANCE);
        filter.addRuleToSet(FactAnalysisRule.INSTANCE);
        return ConditionalFeature.createConditional(filter, cost);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public String toString() {
        return NAME.toString();
    }
}
