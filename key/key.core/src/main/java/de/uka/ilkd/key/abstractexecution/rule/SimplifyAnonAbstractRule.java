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

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.ParametricSkolemLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
import de.uka.ilkd.key.abstractexecution.proof.TermAccessibleLocationsCollector;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;
import org.key_project.util.collection.ImmutableList;

import java.util.Collections;
import java.util.Optional;

/**
 * Drops an anon application from a heap update, if the anonymized location set
 * is disjoint from the locations in the target.
 *
 * <code>
 * hasToOverwrite(frame1, frame2),
 * {disjoint(loc, frame2) | loc \in anonHeapExpr)
 * ->
 * anon(anon(subHeap, frame2, anonHeap),
 * frame1,
 * anonHeapExpr)
 * =
 * anon(subHeap, frame1, anonHeapExpr)
 * </code>
 *
 * @author Dominic Steinhoefel
 */
public class SimplifyAnonAbstractRule implements BuiltInRule {
    public final static SimplifyAnonAbstractRule INSTANCE = new SimplifyAnonAbstractRule();

    private final static Name RULE_NAME = new Name("simplifyAnonAbstract");

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
            throws RuleAbortException {
        if (!(ruleApp instanceof SimplifyAnonAbstractRuleApp) || !ruleApp.complete()) {
            assert false : "Wrong type of, or incomplete, rule application.";
            return null;
        }

        final SimplifyAnonAbstractRuleApp app = (SimplifyAnonAbstractRuleApp) ruleApp;

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

        // \find(anon(anon(subHeap, frame2, anonHeap), frame1, anonHeapExpr))

        final Term t = pio.subTerm();
        final Services services = goal.proof().getServices();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();

        if (t.op() != heapLDT.getAnon() || t.sub(0).op() != heapLDT.getAnon()) {
            return false;
        }

        final Term frame1 = t.sub(1);
        final Term frame2 = t.sub(0).sub(1);

        // hasToOverwrite(frame1, frame2)

        // frame1 == hasTo(frame2)
        if (frame1.op() != locSetLDT.getHasTo() || frame1.sub(0) != frame2) {
            return false;
        }

        // TODO: Could want to consider further cases, like frame1 == hasTo(frame3),
        //       where frame3 is a superset of frame2, or unions.

        // {disjoint(loc, frame2) | loc \in anonHeapExpr)
        final Term anonHeapExpr = t.sub(2);

        final TermAccessibleLocationsCollector collector = //
                new TermAccessibleLocationsCollector( //
                        goal.getLocalSpecificationRepository(),
                        services);
        anonHeapExpr.execPostOrder(collector);

        final ImmutableList<PosInOccurrence> evidence = //
                AbstractExecutionUtils.isRelevant( //
                        AbstractUpdateFactory.abstrUpdateLocFromTerm(frame2, Optional.empty(), services),
                        collector.locations(), Collections.emptySet(), goal, services);

        return evidence != null;
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
    public SimplifyAnonAbstractRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new SimplifyAnonAbstractRuleApp(this, pos);
    }

}
