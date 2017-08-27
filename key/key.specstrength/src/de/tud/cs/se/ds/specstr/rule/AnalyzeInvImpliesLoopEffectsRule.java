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

import static de.tud.cs.se.ds.specstr.util.LogicUtilities.removeLoopInvFormulasFromAntec;
import static de.tud.cs.se.ds.specstr.util.LogicUtilities.retrieveLoopScopeIndices;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Strength analysis rule for assessing the strength of a loop invariant with
 * respect to the actual effects of a loop body.
 * 
 * TODO: A use case for an inner loop will be a preserves case for an outer
 * loop. We have to make sure that we use AnalyzeInvImplies... here and not
 * AnalyzeUseCase.
 *
 * @author Dominic Steinhoefel
 */
public final class AnalyzeInvImpliesLoopEffectsRule
        extends AbstractEffectsAnalysisRule {

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

        return indices.parallelStream().map(lsi -> MergeRuleUtils
                .getUpdateRightSideFor(pio.subTerm().sub(0), lsi))
                .map(rhs -> rhs != null
                        && rhs.equals(services.getTermBuilder().FALSE()))
                .reduce(false, (acc, elem) -> acc || elem);
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

    @Override
    protected List<LocationVariable> varsOfInterest(Goal goal,
            Services services, RuleApp ruleApp) {
        final AnalyzeInvImpliesLoopEffectsRuleApp aiileApp = //
                (AnalyzeInvImpliesLoopEffectsRuleApp) ruleApp;

        return aiileApp.getLocalOuts();
    }

    @Override
    protected Term specTerm(Goal goal, Services services, RuleApp ruleApp) {
        final AnalyzeInvImpliesLoopEffectsRuleApp aiileApp = //
                (AnalyzeInvImpliesLoopEffectsRuleApp) ruleApp;
        return aiileApp.getInvTerm();
    }

    @Override
    protected void performAdditionalAnalysisGoalOps(Goal analysisGoal,
            Goal origGoal, Services services, RuleApp ruleApp) {
        final AnalyzeInvImpliesLoopEffectsRuleApp aiileApp = //
                (AnalyzeInvImpliesLoopEffectsRuleApp) ruleApp;
        final Node loopInvNode = aiileApp.getLoopInvNode();
        removeLoopInvFormulasFromAntec(analysisGoal, loopInvNode);
    }

    @Override
    protected boolean removeHeapVarInAnalysisOfLocVarEffects() {
        return true;
    }

    @Override
    protected String specSatisfiedBranchLabel() {
        return AbstractAnalysisRule.INVARIANT_PRESERVED_BRANCH_LABEL;
    }

}
