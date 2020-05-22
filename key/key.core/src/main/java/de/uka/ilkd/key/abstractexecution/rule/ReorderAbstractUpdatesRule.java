// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.rule;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Pushes an abstract update in a parallel update to the front if it's
 * independent of the respective predecessor. Won't pass by an abstract update
 * the identifier of which is lexically smaller than the one of the considered
 * update, such that eventually, a normal form is reached which is occasionally
 * needed for certain relational proofs with statement reorderings.
 * 
 * @author Dominic Steinhoefel
 */
public class ReorderAbstractUpdatesRule implements BuiltInRule {
    public final static ReorderAbstractUpdatesRule INSTANCE = new ReorderAbstractUpdatesRule();

    private final static Name RULE_NAME = new Name("reorderAbstractUpdate");
//    private final static Map<PosInOccurrence, ReorderAbstractUpdatesRuleApp> appCache = new HashMap<>();

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
            throws RuleAbortException {
        if (!(ruleApp instanceof ReorderAbstractUpdatesRuleApp) || !ruleApp.complete()) {
            assert false : "Wrong type of, or incomplete, rule application.";
            return null;
        }

        final ReorderAbstractUpdatesRuleApp app = (ReorderAbstractUpdatesRuleApp) ruleApp;

        final ImmutableList<Goal> newGoals = goal.split(1);

        final SequentFormula oldSeqFor = app.posInOccurrence().sequentFormula();
        final SequentFormula newSeqFor = new SequentFormula(
                MiscTools.replaceInTerm(oldSeqFor.formula(), app.getSimplifiedTerm().get(), 0,
                        app.posInOccurrence().posInTerm(), services));

        newGoals.head().changeFormula(newSeqFor, app.posInOccurrence());

        return newGoals;
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null || pio.subTerm() == null) {
            return false;
        }

        // Selection has to be an update application of a parallel update including an
        // abstract update
        if (!(pio.subTerm().op() instanceof UpdateApplication)) {
            return false;
        }

        final Term update = UpdateApplication.getUpdate(pio.subTerm());

        if (!MergeRuleUtils.isUpdateNormalForm(update, true)) {
            return false;
        }

        return MergeRuleUtils
                .getElementaryUpdates(update, false, goal.proof().getServices().getTermBuilder())
                .stream().map(Term::op).anyMatch(AbstractUpdate.class::isInstance);

//        /*
//         * Now the lengthy check... Try to create an app. Note that we could also return
//         * true here, but then the rule will appear in the interactive menu although
//         * it's not applicable
//         */
//
//        final ReorderAbstractUpdatesRuleApp app = //
//                createApp(pio, goal.proof().getServices()).tryToInstantiate(goal);
//        final boolean complete = app.complete();
//
//        if (complete) {
//            appCache.put(pio, app);
//        }
//
//        return complete;
    }

    @Override
    public Name name() {
        return RULE_NAME;
    }

    @Override
    public String displayName() {
        return RULE_NAME.toString();
    }

    @Override
    public String toString() {
        return RULE_NAME.toString();
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return true;
    }

    @Override
    public ReorderAbstractUpdatesRuleApp createApp(PosInOccurrence pos, TermServices services) {
//        if (appCache.containsKey(pos)) {
//            return appCache.remove(pos);
//        }

        return new ReorderAbstractUpdatesRuleApp(this, pos);
    }

}
