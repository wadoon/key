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

import java.util.*;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.tud.cs.se.ds.specstr.util.LogicUtilities;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
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

        // TODO: A use case for an inner loop will be a preserves case for an
        // outer loop. We have to make sure that we use AnalyzeInvImplies...
        // here and not AnalyzeUseCase.

        final TermBuilder tb = services.getTermBuilder();

        final AnalyzeInvImpliesLoopEffectsRuleApp aiileApp = //
                (AnalyzeInvImpliesLoopEffectsRuleApp) ruleApp;
        final Term invTerm = aiileApp.getInvTerm();
        final List<LocationVariable> localOuts = aiileApp.getLocalOuts();
        final PosInOccurrence pio = ruleApp.posInOccurrence();
        final Term updateTerm = pio.subTerm().sub(0);
        final Node loopInvNode = aiileApp.getLoopInvNode();

        assert updateTerm.op() instanceof UpdateJunctor;

        final LinkedHashMap<LocationVariable, Term> updateContent =
                LogicUtilities
                        .updateToMap(updateTerm);

        final LocationVariable heapVar = services.getTypeConverter()
                .getHeapLDT().getHeap();

        final LinkedHashMap<LocationVariable, Term> updateLocalOuts = updateContent
                .keySet().stream()
                .filter(lhs -> localOuts.contains(lhs))
                .collect(Collectors.toMap(x -> x, x -> updateContent.get(x),
                        (u, v) -> {
                            throw new IllegalStateException(
                                    String.format("Duplicate key %s", u));
                        }, LinkedHashMap::new));

        // Retrieve store equalities
        final Term origHeapTerm = MergeRuleUtils
                .getUpdateRightSideFor(updateTerm, heapVar);

        final Optional<Pair<Term, List<Term>>> storeEqsAndInnerHeapTerm = //
                extractStoreEqsAndInnerHeapTerm(services, origHeapTerm);

        final List<Term> storeEqualities = storeEqsAndInnerHeapTerm.isPresent()
                ? storeEqsAndInnerHeapTerm.get().second
                : new ArrayList<>();

        final ImmutableList<Goal> goals = goal
                .split(updateLocalOuts.size() + storeEqualities.size() + 1);
        final Goal[] goalArray = goals.toArray(Goal.class);
        final TermLabelState termLabelState = new TermLabelState();

        int i = 0;
        for (LocationVariable currLocalOut : updateLocalOuts.keySet()) {
            final Goal analysisGoal = goalArray[i++];

            final Term updWithoutHeapAndCurrLocal = updateContent.keySet()
                    .stream()
                    .filter(lv -> !lv.equals(heapVar))
                    .filter(lv -> !lv.equals(currLocalOut))
                    .map(lv -> tb.elementary(lv, updateContent.get(lv)))
                    .reduce(tb.skip(), (acc, elem) -> tb.parallel(acc, elem));

            final Term currAnalysisTerm = tb.equals(tb.var(currLocalOut),
                    updateLocalOuts.get(currLocalOut));

            prepareGoal(pio, analysisGoal, currAnalysisTerm, termLabelState,
                    this);
            removeLoopInvFormulasFromAntec(analysisGoal, loopInvNode);
            addFactPreconditions(analysisGoal,
                    ImmutableSLList.<Term> nil()
                            .prepend(storeEqualities)
                            .prepend(tb.apply(updWithoutHeapAndCurrLocal,
                                    invTerm)), //
                    1, termLabelState, this);
        }

        final Term updWithoutHeap = updateContent.keySet().stream()
                .filter(lv -> !lv.equals(heapVar))
                .map(lv -> tb.elementary(lv, updateContent.get(lv)))
                .reduce(tb.skip(), (acc, elem) -> tb.parallel(acc, elem));

        for (Term heapEquality : storeEqualities) {
            final Goal analysisGoal = goalArray[i++];

            prepareGoal(pio, analysisGoal, heapEquality, termLabelState,
                    this);
            removeLoopInvFormulasFromAntec(analysisGoal, loopInvNode);

            final ImmutableList<Term> invNewState = ImmutableSLList.<Term> nil()
                    .prepend(tb.apply(updWithoutHeap, invTerm));

            final ImmutableList<Term> preconds = ImmutableSLList.<Term> nil()
                    .prepend(storeEqualities.stream()
                            .filter(eq -> !eq.equals(heapEquality))
                            .collect(Collectors.toList()))
                    .prepend(invNewState);

            addFactPreconditions(analysisGoal, preconds, 1, termLabelState,
                    this);
        }

        addSETPredicateToAntec(goalArray[goalArray.length - 1]);
        goalArray[goalArray.length - 1].setBranchLabel(
                AbstractAnalysisRule.INVARIANT_PRESERVED_BRANCH_LABEL);

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

        return pio != null && inAnyPreservedCase(pio, services)
                && !(pio.subTerm().sub(1).op() instanceof Modality)
                && !alreadyAnalysisGoal(goal.node().parent());
    }

    private boolean inAnyPreservedCase(PosInOccurrence pio, Services services) {
        final List<LocationVariable> indices = //
                retrieveLoopScopeIndices(pio, services);

        if (indices.isEmpty()) {
            return false;
        }

        for (LocationVariable lsi : indices) {
            final Term rhs = MergeRuleUtils
                    .getUpdateRightSideFor(pio.subTerm().sub(0), lsi);

            if (rhs != null && rhs.equals(services.getTermBuilder().FALSE())) {
                return true;
            }
        }

        return false;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new AnalyzeInvImpliesLoopEffectsRuleApp(this, pos, null, null,
                null);
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
