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

import static de.tud.cs.se.ds.specstr.util.LogicUtilities.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class AnalyzeInvImpliesLoopEffectsRule extends AbstractAnalysisRule {
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

        final LocationVariable heapVar = services.getTypeConverter()
                .getHeapLDT().getHeap();

        final Term updateWithoutLocalOuts = updateContent.keySet().stream()
                .filter(lhs -> !localOuts.contains(lhs))
                .filter(lhs -> !lhs.equals(heapVar))
                .map(lhs -> tb.elementary(lhs, updateContent.get(lhs)))
                .reduce(tb.skip(), (acc, elem) -> tb.parallel(acc, elem));

        // Retrieve store equalities
        final FunctionalOperationContract fContract = //
                getFOContract(services);
        final IProgramMethod pm = fContract.getTarget();
        final Term origHeapTerm = MergeRuleUtils
                .getUpdateRightSideFor(updateTerm, heapVar);

        final Optional<Pair<Term, List<Term>>> storeEqsAndInnerHeapTerm = //
                extractStoreEqsAndInnerHeapTerm( //
                        services, pm, origHeapTerm);

        final List<Term> storeEqualities = storeEqsAndInnerHeapTerm.isPresent()
                ? storeEqsAndInnerHeapTerm.get().second : new ArrayList<>();

        Map<LocationVariable, List<Term>> newGoalInformation = new LinkedHashMap<>();

        for (int i = 0; i < localOuts.size(); i++) {
            final LocationVariable currLocalOut = localOuts.get(i);

            if (updateContent.get(currLocalOut) == null) {
                continue;
            }

            // TODO Excluding the heap here is a hack made because KeY otherwise
            // gets stuck in an endless cascade of equation shuffling
            newGoalInformation
                    .put(currLocalOut,
                            Arrays.asList(new Term[] {
                                    tb.apply(tb.parallel(
                                            tb.elementary(tb.var(heapVar),
                                                    origHeapTerm),
                                            updateWithoutLocalOuts), invTerm),
                                    tb.and(updateContent.keySet().stream()
                                            .filter(lhs -> lhs != currLocalOut)
                                            .filter(lhs -> !lhs.equals(heapVar))
                                            .map(lhs -> tb.equals(tb.var(lhs),
                                                    updateContent.get(lhs)))
                                            .collect(Collectors.toList())) }));
        }

        final ImmutableList<Goal> goals = goal
                .split(newGoalInformation.size() + storeEqualities.size() + 1);
        final Goal[] goalArray = goals.toArray(Goal.class);
        final TermLabelState termLabelState = new TermLabelState();

        int i = 0;
        for (LocationVariable currLocalOut : newGoalInformation.keySet()) {
            final Goal analysisGoal = goalArray[i++];

            final Term currAnalysisTerm = tb.equals(tb.var(currLocalOut),
                    updateContent.get(currLocalOut));

            prepareGoal(pio, analysisGoal, currAnalysisTerm, termLabelState, this);
            removeLoopInvFormulasFromAntec(analysisGoal);
            addFactPreconditions(analysisGoal, newGoalInformation.get(currLocalOut), 1, termLabelState, this);
        }

        if (storeEqsAndInnerHeapTerm.isPresent()) {
            for (Term heapEquality : storeEqualities) {
                final Goal analysisGoal = goalArray[i++];

                prepareGoal(pio, analysisGoal, heapEquality, termLabelState, this);
                removeLoopInvFormulasFromAntec(analysisGoal);

                final Term update = updateWithoutLocalOuts;

                final List<Term> newPres = Arrays.asList(new Term[] { //
                        tb.apply(update, invTerm),
                        tb.and(updateContent.keySet().stream()
                                .filter(lhs -> !lhs.equals(heapVar))
                                .map(lhs -> tb.equals(tb.var(lhs),
                                        updateContent.get(lhs)))
                                .collect(Collectors.toList())),
                        tb.and(storeEqualities.stream()
                                .filter(se -> se != heapEquality)
                                .collect(Collectors.toList())) });

                addFactPreconditions(analysisGoal, newPres, 1, termLabelState, this);
            }
        }

        addSETPredicateToAntec(goalArray[goalArray.length - 1]);
        goalArray[goalArray.length - 1].setBranchLabel(AbstractAnalysisRule.INVARIANT_PRESERVED_BRANCH_LABEL);

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
    public String toString() {
        return displayName();
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        // Rule is applicable if the goal corresponds to one case of the
        // "preserved" part of a loop (scope) invariant rule application; the
        // pio must refer to a formula with a leading update where the loop
        // scope index of the loop is set to FALSE. The formula must have an
        // empty Java block.

        final Services services = goal.proof().getServices();

        Optional<LocationVariable> lsi = null;
        return (lsi = retrieveLoopScopeIndex(pio, services))
                .isPresent()
                && !(pio.subTerm().sub(1).op() instanceof Modality)
                && MergeRuleUtils
                        .getUpdateRightSideFor(pio.subTerm().sub(0), lsi.get())
                        .equals(services.getTermBuilder().FALSE())
                && !alreadyAnalysisGoal(goal.node().parent());
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

    @Override
    public boolean addCoveredWithoutLoopInvGoal() {
        return true;
    }

    @Override
    public boolean addAbstractlyCoveredGoal() {
        return true;
    }

}
