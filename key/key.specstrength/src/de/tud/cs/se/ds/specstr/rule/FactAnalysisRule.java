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

import static de.tud.cs.se.ds.specstr.util.GeneralUtilities.toStream;
import static de.tud.cs.se.ds.specstr.util.LogicUtilities.removeLoopInvFormulasFromAntec;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;

import de.tud.cs.se.ds.specstr.logic.label.StrengthAnalysisParameterlessTL;
import de.tud.cs.se.ds.specstr.util.CNFConverter;
import de.tud.cs.se.ds.specstr.util.GeneralUtilities;
import de.tud.cs.se.ds.specstr.util.LogicUtilities;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Performs a "sub analysis" of one of the other analysis rules; that is,
 * whether a fact is covered, abstractly covered or trivially covered. Not all
 * of these cases apply to all rules, which is why we do a case distinction.
 *
 * @author Dominic Steinhoefel
 */
public final class FactAnalysisRule implements BuiltInRule {

    /**
     * The singleton instance of the {@link FactAnalysisRule}.
     */
    public static final FactAnalysisRule INSTANCE = new FactAnalysisRule();

    /**
     * The branch label for the "abstractly covered" case.
     */
    public static final String FACT_ABSTRACTLY_COVERED_BRANCH_LABEL =
            "Fact abstractly covered (main)";

    /**
     * The branch label for the "abstractly covered check" case.
     */
    public static final String FACT_ABSTRACTLY_COVERED_VERIF_BRANCH_LABEL =
            "Fact abstractly covered (check)";

    /**
     * The branch label for the "trivially covered" case.
     */
    public static final String FACT_COVERED_WITHOUT_SPECIFICATION_BRANCH_LABEL = //
            "Fact covered without specification";

    /**
     * The branch label for the "covered" case.
     */
    public static final String FACT_COVERED_BRANCH_LABEL = "Fact covered";

    /**
     * The {@link Name} of this {@link BuiltInRule}.
     */
    private static final Name NAME = new Name("FactAnalysis");

    private FactAnalysisRule() {
        // Singleton constructor
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {
        final TermBuilder tb = services.getTermBuilder();
        final Node node = goal.node();

        final RuleApp analysisRuleApp = AbstractAnalysisRule
                .analysisRuleAppOfThisScope(node).get();
        final AbstractAnalysisRule abstractAnalysisRule = //
                (AbstractAnalysisRule) analysisRuleApp.rule();
        final boolean addCoveredWithoutLoopInvGoal = abstractAnalysisRule
                .addCoveredWithoutLoopInvGoal();
        final boolean addAbstractlyCoveredGoal = abstractAnalysisRule
                .addAbstractlyCoveredGoal();

        final Optional<SequentFormula> maybeFactSF = toStream(
                node.sequent().succedent())
                        .filter(sf -> sf.formula().containsLabel(
                                StrengthAnalysisParameterlessTL.FACT_LABEL))
                        .findAny();

        assert maybeFactSF.isPresent();

        final SequentFormula factSF = maybeFactSF.get();

        final List<SequentFormula> premiseSFs = toStream(
                node.sequent().antecedent())
                        .filter(sf -> sf.formula().containsLabel(
                                StrengthAnalysisParameterlessTL.FACT_PREMISE_LABEL))
                        .collect(Collectors.toList());

        final Term allPremiseSFs = tb.and(premiseSFs.stream()
                .map(sf -> sf.formula()).collect(Collectors.toList()));
        final CNFConverter cnfC = new CNFConverter(tb);
        final List<Term> premiseConjElems = MergeRuleUtils
                .getConjunctiveElementsFor(cnfC.convertToCNF(allPremiseSFs));

        final ImmutableList<Goal> goals = goal
                .split(1 + (addAbstractlyCoveredGoal ? 2 : 0)
                        + (addCoveredWithoutLoopInvGoal ? 1 : 0));
        final Goal[] goalArray = goals.toArray(new Goal[] {});

        final Goal coveredGoal = goalArray[goalArray.length - 1];
        final Goal coveredByTrueGoal = addCoveredWithoutLoopInvGoal
                ? (addAbstractlyCoveredGoal ? goalArray[2] : goalArray[0])
                : null;
        final Goal abstractlyCoveredGoal = //
                addAbstractlyCoveredGoal ? goalArray[1] : null;
        final Goal abstractlyCoveredVerifGoal = //
                addAbstractlyCoveredGoal ? goalArray[0] : null;

        // The "fully covered" goal

        coveredGoal.setBranchLabel(FACT_COVERED_BRANCH_LABEL);

        // Get the loop invariant node for the following two cases -- needed for
        // the removal of loop invariant formulas
        Node loopInvNode = null;
        if (analysisRuleApp instanceof AnalyzeInvImpliesLoopEffectsRuleApp) {
            loopInvNode =
                    ((AnalyzeInvImpliesLoopEffectsRuleApp) analysisRuleApp)
                            .getLoopInvNode();
        }

        // Fact already covered without specification -- "covered by true"

        if (addCoveredWithoutLoopInvGoal) {
            coveredByTrueGoal.setBranchLabel(
                    FACT_COVERED_WITHOUT_SPECIFICATION_BRANCH_LABEL);

            premiseSFs.forEach(sf -> coveredByTrueGoal.removeFormula(
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), true)));

            removeLoopInvFormulasFromAntec(coveredByTrueGoal, loopInvNode);
        }

        // Facts that are "abstractly covered", that is, the fact with the
        // remaining preconditions implies one of the specification elements, as
        // in "result > 0" is implied by "result = 3"

        if (addAbstractlyCoveredGoal) {
            abstractlyCoveredGoal
                    .setBranchLabel(FACT_ABSTRACTLY_COVERED_BRANCH_LABEL);
            abstractlyCoveredVerifGoal
                    .setBranchLabel(FACT_ABSTRACTLY_COVERED_VERIF_BRANCH_LABEL);

            for (final Goal abstrGoal : new Goal[] { abstractlyCoveredGoal,
                    abstractlyCoveredVerifGoal }) {
                if (addCoveredWithoutLoopInvGoal) {
                    // For these rules, we also have to remove the loop
                    // invariant formulas here
                    removeLoopInvFormulasFromAntec(abstrGoal, loopInvNode);
                }

                LogicUtilities.addSETPredicateToAntec(abstrGoal);

                premiseSFs.forEach(sf -> abstrGoal.removeFormula(
                        new PosInOccurrence(sf, PosInTerm.getTopLevel(),
                                true)));
                abstrGoal.removeFormula(
                        new PosInOccurrence(factSF, PosInTerm.getTopLevel(),
                                false));

                // Add disjunction of premise formula parts to succedent
                abstrGoal.addFormula(
                        new SequentFormula(tb.or(premiseConjElems)), false,
                        true);
            }

            // Add fact to antecedent, not for test goal
            abstractlyCoveredGoal.addFormula(factSF, true, false);
        }

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
        final Node node = goal.node();
        return pio == null && !node.root() && //
                (node.parent().getAppliedRuleApp()
                        .rule() instanceof AbstractAnalysisRule)
                && !node.getNodeInfo().getBranchLabel().equals(
                        AbstractAnalysisRule.INVARIANT_PRESERVED_BRANCH_LABEL)
                && !node.getNodeInfo().getBranchLabel().equals(
                        AbstractAnalysisRule.POSTCONDITION_SATISFIED_BRANCH_LABEL);
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new FactAnalysisRuleApp(this, pos);
    }

    /**
     * @param analysisNodes
     *            The {@link Node}s after an application of
     *            {@link FactAnalysisRule}.
     * @return The "abstactly covered" case {@link Node} of the nodes after a
     *         {@link FactAnalysisRule} application.
     */
    public static Node getFactAbstractlyCoveredNode(
            Iterable<Node> analysisNodes) {
        return getCaseNode(
                FactAnalysisRule.FACT_ABSTRACTLY_COVERED_BRANCH_LABEL,
                analysisNodes);
    }

    /**
     * @param analysisNodes
     *            The {@link Node}s after an application of
     *            {@link FactAnalysisRule}.
     * @return The "abstactly covered test" case {@link Node} of the nodes after
     *         a {@link FactAnalysisRule} application.
     */
    public static Node getFactAbstractlyCoveredVerifNode(
            Iterable<Node> analysisNodes) {
        return getCaseNode(
                FactAnalysisRule.FACT_ABSTRACTLY_COVERED_VERIF_BRANCH_LABEL,
                analysisNodes);
    }

    /**
     * @param analysisNodes
     *            The {@link Node}s after an application of
     *            {@link FactAnalysisRule}.
     * @return The "covered" case {@link Node} of the nodes after a
     *         {@link FactAnalysisRule} application.
     */
    public static Node getFactCoveredNode(Iterable<Node> analysisNodes) {
        return getCaseNode(
                FactAnalysisRule.FACT_COVERED_BRANCH_LABEL,
                analysisNodes);
    }

    /**
     * @param analysisNodes
     *            The {@link Node}s after an application of
     *            {@link FactAnalysisRule}.
     * @return The "trivially covered" case {@link Node} of the nodes after a
     *         {@link FactAnalysisRule} application.
     */
    public static Node getCoveredByTrueNode(Iterable<Node> analysisNodes) {
        return getCaseNode(
                FactAnalysisRule.FACT_COVERED_WITHOUT_SPECIFICATION_BRANCH_LABEL,
                analysisNodes);
    }

    /**
     * @param analysisNodes
     *            The {@link Node}s after an application of
     *            {@link FactAnalysisRule}.
     * @return The case {@link Node} (with the given label) of the nodes after a
     *         {@link FactAnalysisRule} application.
     */
    private static Node getCaseNode(String label,
            Iterable<Node> analysisNodes) {
        assert GeneralUtilities.toStream(analysisNodes).findAny().get().parent()
                .getAppliedRuleApp().rule() == INSTANCE;

        return GeneralUtilities.toStream(analysisNodes)
                .filter(node -> node.getNodeInfo().getBranchLabel().equals(
                        label))
                .findAny().get();
    }

}
