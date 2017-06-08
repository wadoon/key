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

import java.util.List;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;

import de.tud.cs.se.ds.specstr.logic.label.StrengthAnalysisParameterlessTL;
import de.tud.cs.se.ds.specstr.util.CNFConverter;
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
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class FactAnalysisRule implements BuiltInRule {
    private static final Name NAME = new Name("FactAnalysis");
    public static final FactAnalysisRule INSTANCE = new FactAnalysisRule();

    private FactAnalysisRule() {
        // Singleton constructor
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {
        final TermBuilder tb = services.getTermBuilder();
        final Node node = goal.node();

        final SequentFormula factSF = toStream(node.sequent().succedent())
                .filter(sf -> sf.formula().containsLabel(
                        StrengthAnalysisParameterlessTL.FACT_LABEL))
                .findAny().get();

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

        final ImmutableList<Goal> goals = goal.split(3);
        final Goal[] goalArray = goals.toArray(new Goal[] {});
        final Goal coveredGoal = goalArray[2];
        final Goal coveredByTrueGoal = goalArray[1];
        final Goal abstractlyCoveredGoal = goalArray[0];

        coveredGoal.setBranchLabel("Fact covered");
        coveredByTrueGoal.setBranchLabel("Fact covered without specification");
        abstractlyCoveredGoal.setBranchLabel("Fact abstractly covered");

        // Fact already covered without specification -- "covered by true"

        premiseSFs.forEach(sf -> coveredByTrueGoal.removeFormula(
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), true)));

        // Facts that are "abstractly covered", that is, the fact with the
        // remaining preconditions implies one of the specification elements, as
        // in "result > 0" is implied by "result = 3"

        premiseSFs.forEach(sf -> abstractlyCoveredGoal.removeFormula(
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), true)));
        abstractlyCoveredGoal.removeFormula(
                new PosInOccurrence(factSF, PosInTerm.getTopLevel(), false));

        // Add fact to antecedent
        abstractlyCoveredGoal.addFormula(factSF, true, false);

        // Add disjunction of premise formula parts to succedent
        abstractlyCoveredGoal.addFormula(
                new SequentFormula(tb.or(premiseConjElems)), false, true);

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
        Rule rule = null;
        return pio == null && !goal.node().root() && //
                ((rule = goal.node().parent().getAppliedRuleApp()
                        .rule()) == AnalyzeInvImpliesLoopEffectsRule.INSTANCE || //
                        rule == AnalyzePostCondImpliesMethodEffectsRule.INSTANCE);
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

}
