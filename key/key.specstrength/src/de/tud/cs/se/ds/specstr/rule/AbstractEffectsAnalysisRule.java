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

import static de.tud.cs.se.ds.specstr.util.LogicUtilities.addFactPreconditions;
import static de.tud.cs.se.ds.specstr.util.LogicUtilities.addSETPredicateToAntec;
import static de.tud.cs.se.ds.specstr.util.LogicUtilities.extractStoreEqsAndInnerHeapTerm;
import static de.tud.cs.se.ds.specstr.util.LogicUtilities.prepareGoal;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.tud.cs.se.ds.specstr.util.GeneralUtilities;
import de.tud.cs.se.ds.specstr.util.LogicUtilities;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * An {@link AbstractAnalysisRule} for the analysis of the coverage of
 * specification elements (e.g., loop invariants or method post conditions)
 * w.r.t. concrete code effects (update contents).
 *
 * @author Dominic Steinhoefel
 */
public abstract class AbstractEffectsAnalysisRule extends AbstractAnalysisRule {

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {
        final TermBuilder tb = services.getTermBuilder();

        final PosInOccurrence pio = ruleApp.posInOccurrence();
        final Term updateTerm = pio.subTerm().sub(0);

        assert updateTerm.op() instanceof UpdateJunctor;

        final LinkedHashMap<LocationVariable, Term> updateContent =
                LogicUtilities
                        .updateToMap(updateTerm);

        final LinkedHashMap<LocationVariable, Term> updVarOfInterestMap =
                updateContent
                        .keySet().stream()
                        .filter(lhs -> varsOfInterest(goal, services, ruleApp)
                                .contains(lhs))
                        .collect(GeneralUtilities.toLinkedHashMap(x -> x,
                                x -> updateContent.get(x)));

        final LocationVariable heapVar = services.getTypeConverter()
                .getHeapLDT().getHeap();

        // Retrieve store equalities
        final Term origHeapTerm = MergeRuleUtils
                .getUpdateRightSideFor(updateTerm, heapVar);

        final Optional<Pair<Term, List<Term>>> storeEqsAndInnerHeapTerm = //
                extractStoreEqsAndInnerHeapTerm(services, origHeapTerm);

        final List<Term> storeEqualities = storeEqsAndInnerHeapTerm.isPresent()
                ? storeEqsAndInnerHeapTerm.get().second
                : new ArrayList<>();

        final ImmutableList<Goal> goals = goal
                .split(updVarOfInterestMap.size() + storeEqualities.size() + 1);
        final Goal[] goalArray = goals.toArray(Goal.class);
        final TermLabelState termLabelState = new TermLabelState();

        // Mapping from an equation "x = t" to an update which equals the
        // original update, but without the heap and without any elementary
        // update which has the LHS of the equation as update LHS.
        // The equation may be null, then it's ignored.
        final Function<Term, Term> updWithoutHeapAndCurrLocal =
                eq -> updateContent.keySet()
                        .stream()
                        .filter(lv -> !removeHeapVarInAnalysisOfLocVarEffects()
                                || !lv.equals(heapVar))
                        .filter(lv -> eq == null || !lv.equals(eq.sub(0).op()))
                        .map(lv -> tb.elementary(lv, updateContent.get(lv)))
                        .reduce(tb.skip(),
                                (acc, elem) -> tb.parallel(acc, elem));

        final List<Term> locVarAnalysisTerms =
                updVarOfInterestMap.keySet().stream()
                        .map(lv -> tb.equals(tb.var(lv),
                                updVarOfInterestMap.get(lv)))
                        .collect(Collectors.toList());
        
        final List<Term> analysisTerms = new ArrayList<>();
        analysisTerms.addAll(locVarAnalysisTerms);
        analysisTerms.addAll(storeEqualities);

        int i = 0;
        for (Term currAnalysisTerm : analysisTerms) {
            final Goal analysisGoal = goalArray[i++];

            prepareGoal(pio, analysisGoal,
                    currAnalysisTerm, termLabelState,
                    this);

            performAdditionalAnalysisGoalOps(analysisGoal, goal, services,
                    ruleApp);

            {
                final Term specNewState = tb.apply(
                        updWithoutHeapAndCurrLocal.apply(currAnalysisTerm),
                        specTerm(goal, services, ruleApp));

                final ImmutableList<Term> preconds =
                        ImmutableSLList.<Term> nil()
                                .prepend(storeEqualities.stream()
                                        .filter(eq -> !eq
                                                .equals(currAnalysisTerm))
                                        .collect(Collectors.toList()))
                                .prepend(specNewState);

                addFactPreconditions(analysisGoal, preconds, 1, termLabelState,
                        this);
            }
        }

        addSETPredicateToAntec(goalArray[goalArray.length - 1]);
        goalArray[goalArray.length - 1].setBranchLabel(
                specSatisfiedBranchLabel());

        return goals;
    }

    /**
     * The location variables the effects to which should be checked; could be
     * the result variable for a post condition strength analysis, or the "local
     * outs" for a loop body strength analysis.
     * 
     * @param goal
     * @param services
     * @param ruleApp
     *
     * @return The {@link LocationVariable}s that are of interest for this rule.
     * 
     * @see BuiltInRule#apply(Goal, Services, RuleApp) For parameter
     *      explanations
     */
    protected abstract List<LocationVariable> varsOfInterest(Goal goal,
            Services services, RuleApp ruleApp);

    /**
     * @param goal
     * @param services
     * @param ruleApp
     * @return The specification {@link Term}, such as the loop invariant or
     *         method post condition, or (in the future maybe) block contract
     *         post condition.
     * 
     * @see BuiltInRule#apply(Goal, Services, RuleApp) For parameter
     *      explanations
     */
    protected abstract Term specTerm(Goal goal, Services services,
            RuleApp ruleApp);

    /**
     * Perform additional operations on an analysis {@link Goal}, like removing
     * remaining loop invariant formulas that could distract the analysis.
     *
     * @param analysisGoal
     *            The newly created effect analysis {@link Goal}.
     * @param origGoal
     *            The original {@link Goal} passed to this rule.
     * @param services
     * @param ruleApp
     * 
     * @see BuiltInRule#apply(Goal, Services, RuleApp) For parameter
     *      explanations
     */
    protected abstract void performAdditionalAnalysisGoalOps(Goal analysisGoal,
            Goal origGoal, Services services, RuleApp ruleApp);

    /**
     * @return true iff in the update generated for the preconditions in the
     *         analysis of the effects on local variables, the "heap" variable
     *         should be removed.
     */
    protected abstract boolean removeHeapVarInAnalysisOfLocVarEffects();

    /**
     * @return The branch label for the branch checking whether the
     *         specification is satisfied.
     */
    protected abstract String specSatisfiedBranchLabel();

}
