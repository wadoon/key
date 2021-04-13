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

import java.util.List;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
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
 * Drops abstract update to the heap variable if the target is independent of
 * the assigned locations.
 * 
 * <code>
 *      disjoint(locSet1, locSet3) &
 *      disjoint(locSet2, locSet3)
 *    ->
 *        {heap:={U_P(locSet1, locSet2:=footprint)}heap}value(locSet3)
 *      = value(locSet3)
 * </code>
 * 
 * @author Dominic Steinhoefel
 */
public class DropAbstractHeapUpdateRule implements BuiltInRule {
    public final static DropAbstractHeapUpdateRule INSTANCE = new DropAbstractHeapUpdateRule();

    private final static Name RULE_NAME = new Name("dropAbstractHeapUpdate");

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
            throws RuleAbortException {
        if (!(ruleApp instanceof DropAbstractHeapUpdateRuleApp) || !ruleApp.complete()) {
            assert false : "Wrong type of, or incomplete, rule application.";
            return null;
        }

        final DropAbstractHeapUpdateRuleApp app = (DropAbstractHeapUpdateRuleApp) ruleApp;

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

        // \find({ ... || heap:={...||U_P(...:=...)||...}heap || ... } phi(value(...)))

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

        // Assert that there exists exactly one heap update
        final LocationVariable heapVar = heapLDT.getHeap();
        final List<Term> elemHeapUpdateRHSs = MergeRuleUtils
                .getElementaryUpdates(update, services.getTermBuilder()).stream()
                .filter(upd -> upd.op() instanceof ElementaryUpdate)
                .filter(upd -> ((ElementaryUpdate) upd.op()).lhs() == heapVar)
                .map(upd -> upd.sub(0)).collect(Collectors.toList());

        if (elemHeapUpdateRHSs.size() != 1) {
            return false;
        }

        // Assert that the right-hand side of the heap update is itself an
        // update application to the heap variable containing an abstract update
        final Term heapUpdRHS = elemHeapUpdateRHSs.get(0);
        if (heapUpdRHS.op() != UpdateApplication.UPDATE_APPLICATION
                || UpdateApplication.getTarget(heapUpdRHS).op() != heapVar) {
            return false;
        }

        final Term innerUpdate = UpdateApplication.getUpdate(heapUpdRHS);
        if (!MergeRuleUtils.isUpdateNormalForm(innerUpdate, true)
                || MergeRuleUtils.getElementaryUpdates(innerUpdate, services.getTermBuilder())
                        .stream().noneMatch(upd -> upd.op() instanceof AbstractUpdate)) {
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
                && collector.locations().stream().filter(SkolemLoc.class::isInstance)
                        .map(SkolemLoc.class::cast).count() > 0;
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
    public DropAbstractHeapUpdateRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DropAbstractHeapUpdateRuleApp(this, pos);
    }

}
