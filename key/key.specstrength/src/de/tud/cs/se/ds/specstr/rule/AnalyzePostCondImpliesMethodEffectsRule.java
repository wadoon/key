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

import static de.tud.cs.se.ds.specstr.util.LogicUtilities.getFOContract;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

/**
 * Strength analysis rule for assessing the strength of a post condition with
 * respect to the actual effects of the method (modulo abstractions by loop
 * invariants or method calls by contract).
 *
 * @author Dominic Steinhoefel
 */
public final class AnalyzePostCondImpliesMethodEffectsRule
        extends AbstractEffectsAnalysisRule {

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
                && !AnalyzeInvImpliesLoopEffectsRule.INSTANCE.isApplicable(goal,
                        pio)
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

    @Override
    protected List<LocationVariable> varsOfInterest(Goal goal,
            Services services, RuleApp ruleApp) {
        final List<LocationVariable> result = new ArrayList<>();

        final FunctionalOperationContract fContract = //
                getFOContract(services);

        if (!fContract.getTarget().isVoid()) {
            // We have to look the variable up from the current namespaces,
            // since otherwise we will obtain a different object...
            result.add((LocationVariable) goal.getLocalNamespaces()
                    .programVariables()
                    .lookup(fContract.getResult().op().name()));
        }

        return result;
    }

    @Override
    protected Term specTerm(Goal goal, Services services, RuleApp ruleApp) {
        // Note: That's a very hackish way of retrieving the post condition, but
        // I did not find a clean one to get it with the correct variable
        // instantiations
        return TermBuilder.goBelowUpdates(goal.proof().root()
                .sequent().succedent().getFirst().formula().sub(1)).sub(0);
    }

    @Override
    protected void performAdditionalAnalysisGoalOps(Goal analysisGoal,
            Goal origGoal, Services services, RuleApp ruleApp) {
        // We don't do anything
    }

    @Override
    protected boolean removeHeapVarInAnalysisOfLocVarEffects() {
        return false;
    }

    @Override
    protected String specSatisfiedBranchLabel() {
        return AbstractAnalysisRule.POSTCONDITION_SATISFIED_BRANCH_LABEL;
    }
}
