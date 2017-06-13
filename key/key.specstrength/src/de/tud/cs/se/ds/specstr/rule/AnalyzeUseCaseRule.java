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

import java.util.List;
import java.util.Optional;

import org.key_project.util.collection.ImmutableList;

import de.tud.cs.se.ds.specstr.logic.label.StrengthAnalysisParameterlessTL;
import de.tud.cs.se.ds.specstr.util.CNFConverter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class AnalyzeUseCaseRule extends AbstractAnalysisRule {
    public static final Name NAME = new Name("AnalyzeUseCase");
    public static final AnalyzeUseCaseRule INSTANCE = new AnalyzeUseCaseRule();

    private AnalyzeUseCaseRule() {
        // Singleton Constructor
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {
        assert ruleApp instanceof AnalyzeUseCaseRuleApp;

        final TermBuilder tb = services.getTermBuilder();

        final CNFConverter cnfConv = new CNFConverter(tb);
        final Term cnfPostCond = cnfConv
                .convertToCNF(ruleApp.posInOccurrence().subTerm());
        final List<Term> conjElems = MergeRuleUtils
                .getConjunctiveElementsFor(cnfPostCond);

        final ImmutableList<Goal> goals = goal.split(conjElems.size());

        int i = 0;
        for (final Goal newGoal : goals) {
            newGoal.removeFormula(ruleApp.posInOccurrence());
            newGoal.addFormula(
                    new SequentFormula(tb.label(conjElems.get(i),
                            StrengthAnalysisParameterlessTL.FACT_LABEL)),
                    false, false);

            final String factDescr = LogicPrinter.quickPrintTerm( //
                    SymbolicExecutionUtil.improveReadability( //
                            conjElems.get(i), services),
                    services);
            newGoal.node().getNodeInfo()
                    .setBranchLabel(String.format("%s \"%s\"",
                            AbstractAnalysisRule.COVERS_FACT_BRANCH_LABEL_PREFIX,
                            factDescr));

            i++;
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
        return pio != null && pio.isTopLevel() && !pio.isInAntec()
                && !(pio.subTerm().op() instanceof UpdateApplication)
                && !pio.subTerm().containsJavaBlockRecursive()
                && nextParentBranchLabel(goal.node()).orElse("")
                        .equals(AbstractAnalysisRule.POSTCONDITION_SATISFIED_BRANCH_LABEL);
    }

    /**
     * TODO Comment.
     *
     * @param node
     * @return
     */
    private static Optional<String> nextParentBranchLabel(Node node) {
        while (!node.parent().root() && node.parent().childrenCount() < 2) {
            node = node.parent();
        }

        return Optional.ofNullable(node.getNodeInfo().getBranchLabel());
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new AnalyzeUseCaseRuleApp(this, pos);
    }

}
