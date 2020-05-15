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

import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.ParametricSkolemLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
import de.uka.ilkd.key.abstractexecution.proof.TermAccessibleLocationsCollector;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Drops an anon application from a heap update, if the anonymized location set
 * is disjoint from the locations in the target.
 * 
 * <code>
 *     disjoint(frameP, frameQ)
 *   ->
 *       {heap:=anon(subHeap, frameQ, anonFunc)}
 *         value(frameP)
 *     = {heap:=subHeap}
 *         value(frameP)
 * </code>
 * 
 * @author Dominic Steinhoefel
 */
public class DropAnonAbstractRule implements BuiltInRule {
    public final static DropAnonAbstractRule INSTANCE = new DropAnonAbstractRule();

    private final static Name RULE_NAME = new Name("dropAnonAbstract");

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
            throws RuleAbortException {
        if (!(ruleApp instanceof DropAnonAbstractRuleApp) || !ruleApp.complete()) {
            assert false : "Wrong type of, or incomplete, rule application.";
            return null;
        }

        final DropAnonAbstractRuleApp app = (DropAnonAbstractRuleApp) ruleApp;

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

        // \find({ ... || heap:=anon(...) || ...} phi(value(...)))

        final Term t = pio.subTerm();
        final Services services = goal.proof().getServices();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        if (t.op() != UpdateApplication.UPDATE_APPLICATION) {
            return false;
        }

        final Term update = UpdateApplication.getUpdate(t);
        if (!MergeRuleUtils.isUpdateNormalForm(update, true)) {
            return false;
        }

        // Assert that there exists a heap update
        final LocationVariable heapVar = heapLDT.getHeap();
        if (!MergeRuleUtils.getElementaryUpdates(update, services.getTermBuilder()).stream()
                .map(Term::op).filter(ElementaryUpdate.class::isInstance)
                .map(ElementaryUpdate.class::cast).map(ElementaryUpdate::lhs)
                .anyMatch(lhs -> lhs == heapVar)) {
            return false;
        }

        // Assert that the "heap" program variable is not in the target,
        // and that there is some abstract location set in the target.
        final Term target = UpdateApplication.getTarget(t);
        final TermAccessibleLocationsCollector collector = //
                new TermAccessibleLocationsCollector(goal.getLocalSpecificationRepository(),
                        services);
        target.execPostOrder(collector);

        return !collector.locations().stream().filter(PVLoc.class::isInstance)
                .map(PVLoc.class::cast).map(PVLoc::getVar).anyMatch(var -> var == heapVar)
                && collector.locations().stream().filter(
                        loc -> loc instanceof SkolemLoc || loc instanceof ParametricSkolemLoc)
                        .count() > 0;
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
    public DropAnonAbstractRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DropAnonAbstractRuleApp(this, pos);
    }

}
