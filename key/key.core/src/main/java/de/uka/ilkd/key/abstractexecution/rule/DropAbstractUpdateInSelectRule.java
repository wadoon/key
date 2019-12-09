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
import de.uka.ilkd.key.ldt.HeapLDT;
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
 * Drops an abstract update in a select term, if the selected field is proven to
 * not be element of the frame of the abstract update.
 * 
 * <code>
 * !elementOf(o,f,frame) ->
 *   G::select({... || U_P(frame:=...) || ...}h, o, f) =
 *   G::select({... || ... }h, o, f)
 * </code>
 * 
 * @author Dominic Steinhoefel
 */
public class DropAbstractUpdateInSelectRule implements BuiltInRule {
    public final static DropAbstractUpdateInSelectRule INSTANCE = new DropAbstractUpdateInSelectRule();

    private final static Name RULE_NAME = new Name("dropAbstractUpdateInSelect");

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
            throws RuleAbortException {
        if (!(ruleApp instanceof DropAbstractUpdateInSelectRuleApp) || !ruleApp.complete()) {
            assert false : "Wrong type of, or incomplete, rule application.";
            return null;
        }

        final DropAbstractUpdateInSelectRuleApp app = (DropAbstractUpdateInSelectRuleApp) ruleApp;

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

        // \find(G::select({... || U_P(...:=...) || ...}h, o, f))

        final Term t = pio.subTerm();
        final Services services = goal.proof().getServices();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        if (!heapLDT.isSelectOp(t.op())) {
            return false;
        }

        final Term heapTerm = t.sub(0);

        if (heapTerm.op() != UpdateApplication.UPDATE_APPLICATION || UpdateApplication
                .getTarget(heapTerm).op() == UpdateApplication.UPDATE_APPLICATION) {
            return false;
        }

        return MergeRuleUtils
                .getElementaryUpdates(UpdateApplication.getUpdate(heapTerm), false,
                        services.getTermBuilder())
                .stream().map(Term::op).anyMatch(AbstractUpdate.class::isInstance);
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
    public DropAbstractUpdateInSelectRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DropAbstractUpdateInSelectRuleApp(this, pos);
    }

}
