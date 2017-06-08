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

package de.tud.cs.se.ds.specstr.profile;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.tud.cs.se.ds.specstr.rule.AnalyzeInvImpliesLoopEffectsRule;
import de.tud.cs.se.ds.specstr.rule.AnalyzePostCondImpliesMethodEffectsRule;
import de.tud.cs.se.ds.specstr.rule.FactAnalysisRule;
import de.tud.cs.se.ds.specstr.strategy.StrengthAnalysisStrategy;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class StrengthAnalysisSEProfile extends SymbolicExecutionJavaProfile {
    public static final String NAME = "Java Profile for Strength Analysis";
    public static final StrengthAnalysisSEProfile INSTANCE = new StrengthAnalysisSEProfile();

    /**
     * The used {@link StrategyFactory} of the {@link StrengthAnalysisStrategy}.
     */
    private final static StrategyFactory STRENGTH_ANALYSIS_FACTORY = //
            new StrengthAnalysisStrategy.Factory();

    /**
     * @param predicateEvaluationEnabled
     */
    private StrengthAnalysisSEProfile() {
        super(true);
    }

    @Override
    protected ImmutableList<BuiltInRule> initBuiltInRules() {
        return super.initBuiltInRules()
                .append(AnalyzeInvImpliesLoopEffectsRule.INSTANCE)
                .append(AnalyzePostCondImpliesMethodEffectsRule.INSTANCE)
                .append(FactAnalysisRule.INSTANCE);
    }

    @Override
    protected ImmutableSet<StrategyFactory> getStrategyFactories() {
        ImmutableSet<StrategyFactory> set = super.getStrategyFactories();
        set = set.add(STRENGTH_ANALYSIS_FACTORY);
        return set;
    }

    @Override
    public String name() {
        return NAME;
    }

}
