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

import org.key_project.util.collection.ImmutableList;

import de.tud.cs.se.ds.specstr.util.LogicUtilities;
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
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Strength analysis rule for assessing the strength of a loop invariant with
 * respect to the actual effects of a loop body.
 *
 * @author Dominic Steinhöfel
 */
public final class AnalyzeInvImpliesLoopEffectsRule
        extends AbstractAnalysisRule {

    /**
     * The {@link Name} of this {@link AbstractAnalysisRule}.
     */
    public static final Name NAME = new Name("AnalyzeInvImpliesLoopEffects");

    /**
     * Singleton instance of the {@link AnalyzeInvImpliesLoopEffectsRule}.
     */
    public static final AnalyzeInvImpliesLoopEffectsRule INSTANCE = //
            new AnalyzeInvImpliesLoopEffectsRule();

    /**
     * Singleton constructor.
     */
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

        final Map<LocationVariable, Term> updateContent = LogicUtilities
                .updateToMap(updateTerm);

        final LocationVariable heapVar = services.getTypeConverter()
                .getHeapLDT().getHeap();

        final Term updateWithoutLocalOuts = updateContent.keySet().stream()
                .filter(lhs -> !localOuts.contains(lhs))
                .filter(lhs -> !lhs.equals(heapVar))
                .map(lhs -> tb.elementary(lhs, updateContent.get(lhs)))
                .reduce(tb.skip(), (acc, elem) -> tb.parallel(acc, elem));

        // Retrieve store equalities
        final IProgramMethod pm = getFOContract(services).getTarget();
        final Term origHeapTerm = MergeRuleUtils
                .getUpdateRightSideFor(updateTerm, heapVar);

        final Optional<Pair<Term, List<Term>>> storeEqsAndInnerHeapTerm = //
                extractStoreEqsAndInnerHeapTerm(//
                    services, pm, origHeapTerm);

        final List<Term> storeEqualities = storeEqsAndInnerHeapTerm.isPresent()
                ? storeEqsAndInnerHeapTerm.get().second : new ArrayList<>();

        final Map<LocationVariable, List<Term>> newGoalInformation = constructNewGoalInformation(
            tb, invTerm, localOuts, updateContent, heapVar,
            updateWithoutLocalOuts, origHeapTerm);

        final ImmutableList<Goal> goals = goal
                .split(newGoalInformation.size() + storeEqualities.size() + 1);
        final Goal[] goalArray = goals.toArray(Goal.class);
        final TermLabelState termLabelState = new TermLabelState();

        int i = 0;
        for (LocationVariable currLocalOut : newGoalInformation.keySet()) {
            final Goal analysisGoal = goalArray[i++];

            final Term currAnalysisTerm = tb.equals(tb.var(currLocalOut),
                updateContent.get(currLocalOut));

            prepareGoal(pio, analysisGoal, currAnalysisTerm, termLabelState,
                this);
            removeLoopInvFormulasFromAntec(analysisGoal);
            addFactPreconditions(analysisGoal,
                newGoalInformation.get(currLocalOut), //
                1, termLabelState, this);
        }

        if (storeEqsAndInnerHeapTerm.isPresent()) {
            for (Term heapEquality : storeEqualities) {
                final Goal analysisGoal = goalArray[i++];

                prepareGoal(pio, analysisGoal, heapEquality, termLabelState,
                    this);
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

                addFactPreconditions(analysisGoal, newPres, 1, termLabelState,
                    this);
            }
        }

        addSETPredicateToAntec(goalArray[goalArray.length - 1]);
        goalArray[goalArray.length - 1].setBranchLabel(
            AbstractAnalysisRule.INVARIANT_PRESERVED_BRANCH_LABEL);

        return goals;
    }

    /**
     * The "new goal information" is a map from a "local out" to a list of two
     * elements: the loop invariant in the original heap state and the local
     * state without all "localOuts", and a conjunction of all facts without the
     * current "local out".
     *
     * @param tb
     *            The {@link TermBuilder} object.
     * @param invTerm
     *            The loop invariant {@link Term} (without update).
     * @param localOuts
     *            The "local outs", i.e. variables that are available also
     *            outside the loop.
     * @param updateContent
     *            The disassembled update.
     * @param heapVar
     *            The heap {@link LocationVariable}.
     * @param updateWithoutLocalOuts
     *            The update without all local outs.
     * @param origHeapTerm
     *            The original heap term.
     * @return A map from a "local out" to a list of two elements: the loop
     *         invariant in the original heap state and the local state without
     *         all "localOuts", and a conjunction of all facts without the
     *         current "local out".
     */
    private Map<LocationVariable, List<Term>> constructNewGoalInformation(
            final TermBuilder tb, final Term invTerm,
            final List<LocationVariable> localOuts,
            final Map<LocationVariable, Term> updateContent,
            final LocationVariable heapVar, final Term updateWithoutLocalOuts,
            final Term origHeapTerm) {
        final Map<LocationVariable, List<Term>> newGoalInformation = new LinkedHashMap<>();

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
                            // The loop invariant in the original heap state and
                            // the local state without the "localOuts"
                            tb.apply(
                                tb.parallel(tb.elementary(tb.var(heapVar),
                                    origHeapTerm), updateWithoutLocalOuts),
                                invTerm),
                            // The collected equations
                            tb.and(updateContent.keySet().stream()
                                    .filter(lhs -> lhs != currLocalOut)
                                    .filter(lhs -> !lhs.equals(heapVar))
                                    .map(lhs -> tb.equals(tb.var(lhs),
                                        updateContent.get(lhs)))
                                    .collect(Collectors.toList())) }));
        }

        return newGoalInformation;
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
        return (lsi = retrieveLoopScopeIndex(pio, services)).isPresent()
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

    @Override
    public boolean addCoveredWithoutLoopInvGoal() {
        return true;
    }

    @Override
    public boolean addAbstractlyCoveredGoal() {
        return true;
    }

}
