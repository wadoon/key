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
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Strength analysis rule for assessing the strength of a post condition with
 * respect to the actual effects of the method (modulo abstractions by loop
 * invariants or method calls by contract).
 *
 * @author Dominic Steinhöfel
 */
public final class AnalyzePostCondImpliesMethodEffectsRule
        extends AbstractAnalysisRule {

    /**
     * The {@link Name} of this {@link AbstractAnalysisRule}.
     */
    public static final Name NAME = new Name(
        "AnalyzePostCondImpliesMethodEffects");

    /**
     * Singleton instance of the
     * {@link AnalyzePostCondImpliesMethodEffectsRule}.
     */
    public static final AnalyzePostCondImpliesMethodEffectsRule INSTANCE = //
            new AnalyzePostCondImpliesMethodEffectsRule();

    private AnalyzePostCondImpliesMethodEffectsRule() {
        // Singleton Constructor
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {
        final TermBuilder tb = services.getTermBuilder();

        final PosInOccurrence pio = ruleApp.posInOccurrence();
        final Term updateTerm = pio.subTerm().sub(0);
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LocationVariable heapVar = heapLDT.getHeap();

        final FunctionalOperationContract fContract = //
                getFOContract(services);

        // Note: That's a very hackish way of retrieving the post condition, but
        // I did not find a clean one to get it with the correct variable
        // instantiations
        final Term contract = TermBuilder.goBelowUpdates(goal.proof().root()
                .sequent().succedent().getFirst().formula().sub(1)).sub(0);

        final IProgramMethod pm = fContract.getTarget();
        boolean isVoid = pm.isVoid();

        // The variables that we're interested in are the heap (for non-static,
        // non-pure methods) and the result variable (for non-void methods),
        // because changes to them describe the method's behavior
        final Term origHeapTerm = MergeRuleUtils
                .getUpdateRightSideFor(updateTerm, heapVar);
        final boolean hasHeap = origHeapTerm != null;

        final Optional<Pair<Term, List<Term>>> storeEqsAndInnerHeapTerm = //
                extractStoreEqsAndInnerHeapTerm(//
                    services, origHeapTerm);

        final List<Term> storeEqualities = hasHeap
                ? storeEqsAndInnerHeapTerm.get().second : new ArrayList<>();

        // We have to look the variable up from the current namespaces, since
        // otherwise we will obtain a different object...
        final LocationVariable resultVar = isVoid ? null
                : (LocationVariable) goal.getLocalNamespaces()
                        .programVariables()
                        .lookup(fContract.getResult().op().name());

        final Map<LocationVariable, Term> updateContent = LogicUtilities
                .updateToMap(updateTerm);

        final boolean hasResultVar = resultVar != null
                && updateContent.get(resultVar) != null;

        final Term updateWithoutVarsOfInterest = updateContent.keySet().stream()
                .filter(lhs -> isVoid || !lhs.equals(resultVar))
                .filter(lhs -> !lhs.equals(heapVar))
                .map(lhs -> tb.elementary(lhs, updateContent.get(lhs)))
                .reduce(tb.skip(), (acc, elem) -> tb.parallel(acc, elem));

        final ImmutableList<Goal> goals = goal
                .split((hasResultVar ? 1 : 0) + storeEqualities.size() + 1);
        final Goal[] goalArray = goals.toArray(Goal.class);
        final TermLabelState termLabelState = new TermLabelState();

        // Add result var goal
        if (hasResultVar) {
            final Goal analysisGoal = goalArray[0];

            final Term currAnalysisTerm = tb.equals(tb.var(resultVar),
                MergeRuleUtils.getUpdateRightSideFor(updateTerm, resultVar));

            prepareGoal(pio, analysisGoal, currAnalysisTerm, termLabelState,
                this);

            final List<Term> newPres = Arrays
                    .asList(new Term[] {
                        tb.apply(hasHeap
                                ? tb.parallel(
                                    tb.elementary(tb.var(heapVar),
                                        origHeapTerm),
                                    updateWithoutVarsOfInterest)
                                : updateWithoutVarsOfInterest,
                            contract),
                        tb.and(updateContent.keySet().stream()
                                .filter(lhs -> lhs != resultVar)
                                .filter(lhs -> !lhs.equals(heapVar))
                                .map(lhs -> tb.equals(tb.var(lhs),
                                    updateContent.get(lhs)))
                                .collect(Collectors.toList())) });

            addFactPreconditions(analysisGoal, newPres, 1, termLabelState,
                this);
        }

        int i = hasResultVar ? 1 : 0;

        // Add goals for store equalities
        if (hasHeap) {
            final Term innerHeapTerm = storeEqsAndInnerHeapTerm.get().first;

            for (Term storeEquality : storeEqualities) {
                final Goal analysisGoal = goalArray[i];

                prepareGoal(pio, analysisGoal, storeEquality, termLabelState,
                    this);

                final Term update = tb.parallel(//
                    tb.elementary(tb.var(heapVar), innerHeapTerm), //
                    updateWithoutVarsOfInterest);

                final List<Term> newPres = Arrays
                        .asList(new Term[] { tb.apply(update, contract),
                            tb.and(updateContent.keySet().stream()
                                    .filter(lhs -> !lhs.equals(heapVar))
                                    .map(lhs -> tb.equals(tb.var(lhs),
                                        updateContent.get(lhs)))
                                    .collect(Collectors.toList())) });

                addFactPreconditions(analysisGoal, newPres, 1, termLabelState,
                    this);

                i++;
            }
        }

        // Remove SETAccumulate predicate for post condition
        final Goal postCondGoal = goalArray[goalArray.length - 1];
        addSETPredicateToAntec(postCondGoal);

        postCondGoal.setBranchLabel(
            AbstractAnalysisRule.POSTCONDITION_SATISFIED_BRANCH_LABEL);

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
        Term f = null;

        // We exclude facts for sequents of type "\Gamma ==> \Delta, {U}false",
        // those are irrelevant for us.

        return pio != null && pio.isTopLevel() && !pio.isInAntec()
                && !(f = pio.subTerm()).containsJavaBlockRecursive()
                && f.op() instanceof UpdateApplication
                && !(f.sub(1).op() instanceof Modality)
                && !TermBuilder.goBelowUpdates(f).op().equals(Junctor.FALSE)
                && !AnalyzeInvImpliesLoopEffectsRule.INSTANCE.isApplicable(goal, pio)
                && (goal.node().getNodeInfo().getBranchLabel() == null
                        || !goal.node().getNodeInfo().getBranchLabel()
                                .equals(LoopScopeInvariantRule. //
                                        INVARIANT_INITIALLY_VALID_BRANCH_LABEL))
                && !AbstractAnalysisRule
                        .alreadyAnalysisGoal(goal.node().parent());
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new AnalyzePostCondImpliesMethodEffectsRuleApp(this, pos);
    }

    @Override
    public boolean addCoveredWithoutLoopInvGoal() {
        return false;
    }

    @Override
    public boolean addAbstractlyCoveredGoal() {
        return true;
    }

}
