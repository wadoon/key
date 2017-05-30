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

package de.uka.ilkd.key.rule.strengthanalysis;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class AnalyzeInvImpliesLoopEffectsRule implements BuiltInRule {
    public static final Name NAME = new Name("AnalyzeInvImpliesLoopEffects");
    public static final AnalyzeInvImpliesLoopEffectsRule INSTANCE = new AnalyzeInvImpliesLoopEffectsRule();

    private AnalyzeInvImpliesLoopEffectsRule() {
        // Singleton Constructor
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {
        assert ruleApp instanceof AnalyzeInvImpliesLoopEffectsRuleApp;

        final TermBuilder tb = services.getTermBuilder();

        final AnalyzeInvImpliesLoopEffectsRuleApp aiileApp = //
                (AnalyzeInvImpliesLoopEffectsRuleApp) ruleApp;
        final Term invTerm = aiileApp.getInvTerm();
        final List<LocationVariable> localOuts = aiileApp.getLocalOuts();
        final PosInOccurrence pio = ruleApp.posInOccurrence();
        final Term updateTerm = pio.subTerm().sub(0);

        assert updateTerm.op() instanceof UpdateJunctor;

        final Map<LocationVariable, Term> updateContent = StreamSupport
                .stream( //
                        MergeRuleUtils.getUpdateLeftSideLocations(updateTerm)
                                .spliterator(),
                        true)
                .collect(Collectors.toMap(
                        lhs -> lhs, lhs -> MergeRuleUtils
                                .getUpdateRightSideFor(updateTerm, lhs),
                        (u, v) -> {
                            throw new IllegalStateException(
                                    String.format("Duplicate key %s", u));
                        }, LinkedHashMap::new));

        final Term updateWithoutLocalOuts = updateContent.keySet().stream()
                .filter(lhs -> !localOuts.contains(lhs))
                .map(lhs -> tb.elementary(lhs, updateContent.get(lhs)))
                .reduce(tb.skip(), (acc, elem) -> tb.parallel(acc, elem));

        final ImmutableList<Goal> goals = goal.split(localOuts.size() + 1);

        final Goal[] goalArray = goals.toArray(Goal.class);

        for (int i = 0; i < localOuts.size(); i++) {
            final LocationVariable currLocalOut = localOuts.get(i);
            final Term currAnalysisTerm = tb.equals(tb.var(currLocalOut),
                    updateContent.get(currLocalOut));

            final Goal analysisGoal = goalArray[i];

            analysisGoal
                    .setBranchLabel(
                            "Covers fact \""
                                    + LogicPrinter
                                            .quickPrintTerm(currAnalysisTerm,
                                                    services)
                                            .replaceAll("(\\r|\\n|\\r\\n)+", "")
                                    + "\"");

            analysisGoal.removeFormula(pio);
            analysisGoal.addFormula(new SequentFormula(currAnalysisTerm), //
                    false, true);
            analysisGoal.addFormula(
                    new SequentFormula(
                            tb.apply(updateWithoutLocalOuts, invTerm)),
                    true, true);
            // TODO Excluding the heap here is a hack made because KeY otherwise
            // gets stuck in an endless cascade of equation shuffling
            analysisGoal.addFormula(
                    new SequentFormula(tb.and(updateContent.keySet().stream()
                            .filter(lhs -> lhs != currLocalOut)
                            .filter(lhs -> !lhs.sort().name().toString()
                                    .equals("Heap"))
                            .map(lhs -> tb.equals(tb.var(lhs),
                                    updateContent.get(lhs)))
                            .collect(Collectors.toList()))),
                    true, true);
        }

        goalArray[goalArray.length - 1].setBranchLabel("Invariant preserved");

        return goals;
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
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        // TODO Refine
        return pio != null && pio.isTopLevel()
                && pio.subTerm().op() instanceof UpdateApplication;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new AnalyzeInvImpliesLoopEffectsRuleApp(this, pos, null, null);
    }

    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services,
            Term invTerm, List<LocationVariable> localOuts) {
        return new AnalyzeInvImpliesLoopEffectsRuleApp(this, pos, invTerm,
                localOuts);
    }

}
