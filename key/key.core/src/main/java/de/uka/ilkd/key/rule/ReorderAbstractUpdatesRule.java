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
package de.uka.ilkd.key.rule;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.MiscTools;

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
                        app.getPioToReplace().posInTerm(), services));

        newGoals.head().changeFormula(newSeqFor, app.posInOccurrence());

        return newGoals;
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null || pio.subTerm() == null) {
            return false;
        }

        // Selection has to be an abstract update inside a parallel update
        if (!(pio.subTerm().op() instanceof AbstractUpdate)) {
            return false;
        }

        if (pio.up().subTerm().op() != UpdateJunctor.PARALLEL_UPDATE) {
            return false;
        }

        return true;
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
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new ReorderAbstractUpdatesRuleApp(this, pos);
    }

}
