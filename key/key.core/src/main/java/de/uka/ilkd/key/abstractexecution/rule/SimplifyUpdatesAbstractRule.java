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

import java.util.HashMap;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
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
import de.uka.ilkd.key.rule.conditions.DropEffectlessElementariesCondition;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Simplifies updates in the presence of abstract location sets; i.e., a
 * generalization of what {@link DropEffectlessElementariesCondition} is doing
 * for location variables.
 * 
 * <p>
 * The rule is applicable on update applications, where either the targets have
 * to contain {@link AbstractUpdateLoc}s that are not {@link PVLoc}s, or the
 * update has to contain {@link AbstractUpdate}s with left-hand sides that are
 * not {@link PVLoc}s.
 * 
 * @author Dominic Steinhoefel
 */
public class SimplifyUpdatesAbstractRule implements BuiltInRule {
    public final static SimplifyUpdatesAbstractRule INSTANCE = new SimplifyUpdatesAbstractRule();

    private final static Name RULE_NAME = new Name("simplifyUpdatesAbstract");
    private final static Map<PosInOccurrence, SimplifyUpdatesAbstractRuleApp> appCache = new HashMap<>();

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
            throws RuleAbortException {
        if (!(ruleApp instanceof SimplifyUpdatesAbstractRuleApp) || !ruleApp.complete()) {
            assert false : "Wrong type of, or incomplete, rule application.";
            return null;
        }

        final SimplifyUpdatesAbstractRuleApp app = (SimplifyUpdatesAbstractRuleApp) ruleApp;

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

        final Term t = pio.subTerm();

        if (t.op() != UpdateApplication.UPDATE_APPLICATION) {
            return false;
        }

        final SimplifyUpdatesAbstractRuleApp app = //
                createApp(pio, goal.proof().getServices()).tryToInstantiate(goal);
        final boolean complete = app.complete();

        if (complete) {
            appCache.put(pio, app);
        }

        return complete;
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
    public SimplifyUpdatesAbstractRuleApp createApp(PosInOccurrence pos, TermServices services) {
        if (appCache.containsKey(pos)) {
            return appCache.remove(pos);
        }

        return new SimplifyUpdatesAbstractRuleApp(this, pos);
    }

}