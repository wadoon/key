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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class AnalyzePostCondImpliesMethodEffectsRule implements BuiltInRule {
    public static final Name NAME = new Name(
            "AnalyzePostCondImpliesMethodEffects");
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

        final ContractPO contractPO = services.getSpecificationRepository()
                .getContractPOForProof(goal.proof());
        assert contractPO != null
                && contractPO instanceof FunctionalOperationContractPO;
        final FunctionalOperationContract fContract = //
                ((FunctionalOperationContractPO) contractPO).getContract();

        // Note: That's a very hackish way of retrieving the post condition, but
        // I did not find a clean one to get it with the correct variable
        // instantiations
        final Term contract = TermBuilder.goBelowUpdates(goal.proof().root()
                .sequent().succedent().getFirst().formula().sub(1)).sub(0);
        // Term contract = fContract.getPost();

        final IProgramMethod pm = fContract.getTarget();

        // The variables that we're interested in are the heap (for non-static,
        // non-pure methods) and the result variable (for non-void methods),
        // because changes to them describe the method's behavior
        final List<Term> storeEqualities = new ArrayList<>();
        final Term origHeapTerm = MergeRuleUtils
                .getUpdateRightSideFor(updateTerm, heapVar);
        Term innerHeapTerm = origHeapTerm;
        if (!pm.isStatic()) {
            // TODO Should we also check whether pm is pure? How to do this?

            // TODO: Is it justified to assume that a heap is of the form
            // store(store(...(anon/heap...))), i.e. if there is a store, then
            // we have a store sequence at the beginning?
            Term currHeapTerm = innerHeapTerm;
            while (currHeapTerm.op() == heapLDT.getStore()) {
                final Term targetObj = currHeapTerm.sub(1);
                final Term field = currHeapTerm.sub(2);
                final Term value = currHeapTerm.sub(3);

                storeEqualities.add(tb.equals(tb.select(value.sort(),
                        tb.getBaseHeap(), targetObj, field), value));

                currHeapTerm = currHeapTerm.sub(0);
            }

            // Here, currHeapTerm should be the "core" without any stores.
            innerHeapTerm = currHeapTerm;
        }

        final LocationVariable resultVar = pm.isVoid() ? null
                : (LocationVariable) fContract.getResult().op();

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

        final Term updateWithoutVarsOfInterest = updateContent.keySet().stream()
                .filter(lhs -> pm.isVoid() || lhs.equals(resultVar))
                .filter(lhs -> !lhs.equals(heapVar))
                .map(lhs -> tb.elementary(lhs, updateContent.get(lhs)))
                .reduce(tb.skip(), (acc, elem) -> tb.parallel(acc, elem));

        final ImmutableList<Goal> goals = goal.split(
                (resultVar == null ? 0 : 1) + storeEqualities.size() + 1);
        final Goal[] goalArray = goals.toArray(Goal.class);

        if (resultVar != null) {
            final Goal analysisGoal = goalArray[0];

            final Term currAnalysisTerm = tb.equals(tb.var(resultVar),
                    MergeRuleUtils.getUpdateRightSideFor(updateTerm,
                            resultVar));

            AnalyzeInvImpliesLoopEffectsRule.prepareGoal(pio, analysisGoal,
                    currAnalysisTerm);

            final List<Term> newPres = Arrays
                    .asList(new Term[] {
                            tb.apply(
                                    tb.parallel(
                                            tb.elementary(tb.var(heapVar),
                                                    origHeapTerm),
                                            updateWithoutVarsOfInterest),
                                    contract),
                            tb.and(updateContent.keySet().stream()
                                    .filter(lhs -> lhs != resultVar)
                                    .filter(lhs -> !lhs.equals(heapVar))
                                    .map(lhs -> tb.equals(tb.var(lhs),
                                            updateContent.get(lhs)))
                                    .collect(Collectors.toList())) });

            newPres.forEach(t -> analysisGoal.addFormula(new SequentFormula(t),
                    true, true));
        }

        int i = 0;
        for (Term storeEquality : storeEqualities) {
            final Goal analysisGoal = goalArray[i
                    + (resultVar == null ? 0 : 1)];

            AnalyzeInvImpliesLoopEffectsRule.prepareGoal(pio, analysisGoal,
                    storeEquality);

            final Term update = tb.parallel( //
                    tb.elementary(tb.var(heapVar), innerHeapTerm), //
                    updateWithoutVarsOfInterest);

            final List<Term> newPres = Arrays
                    .asList(new Term[] { tb.apply(update, contract),
                            tb.and(updateContent.keySet().stream()
                                    .filter(lhs -> !lhs.equals(heapVar))
                                    .map(lhs -> tb.equals(tb.var(lhs),
                                            updateContent.get(lhs)))
                                    .collect(Collectors.toList())) });

            newPres.forEach(t -> analysisGoal.addFormula(new SequentFormula(t),
                    true, true));

            i++;
        }

        goalArray[goalArray.length - 1]
                .setBranchLabel("Postcondition satisfied");

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
        final TermBuilder tb = goal.proof().getServices().getTermBuilder();

        Optional<LocationVariable> lsi = null;
        Term f = null;

        return pio != null && pio.isTopLevel() && !pio.isInAntec()
                && !(f = pio.subTerm()).containsJavaBlockRecursive()
                && f.op() instanceof UpdateApplication
                && (!(lsi = AnalyzeInvImpliesLoopEffectsRule
                        .retrieveLoopScopeIndex(pio,
                                goal.proof().getServices())).isPresent()
                        || MergeRuleUtils
                                .getUpdateRightSideFor(f.sub(0), lsi.get())
                                .equals(tb.TRUE()));
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

}
