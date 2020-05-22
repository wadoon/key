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

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.DefaultBuiltInRuleApp;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.conditions.DropEffectlessElementariesCondition;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * {@link RuleApp} for the {@link ReorderAbstractUpdatesRule}.
 * 
 * @author Dominic Steinhoefel
 */
public class ReorderAbstractUpdatesRuleApp extends DefaultBuiltInRuleApp {
    private ImmutableList<PosInOccurrence> ifInsts = ImmutableSLList.<PosInOccurrence>nil();
    private boolean complete = false;
    private Optional<Term> simplifiedTerm = Optional.empty();

    // ///////////////////////////////////////////////// //
    // //////////////// PUBLIC INTERFACE /////////////// //
    // ///////////////////////////////////////////////// //

    public ReorderAbstractUpdatesRuleApp(BuiltInRule builtInRule, PosInOccurrence pio) {
        super(builtInRule, pio);
    }

    public ReorderAbstractUpdatesRuleApp(BuiltInRule builtInRule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts) {
        super(builtInRule, pio, ifInsts);
        this.ifInsts = ifInsts;
    }

    @Override
    public boolean complete() {
        return complete && super.complete();
    }

    @Override
    public ImmutableList<PosInOccurrence> ifInsts() {
        return ifInsts;
    }

    /**
     * @return the simplified {@link Term}, if any. Should be present iff
     *         {@link #complete()} is true.
     */
    public Optional<Term> getSimplifiedTerm() {
        return simplifiedTerm;
    }

    @Override
    public ReorderAbstractUpdatesRuleApp tryToInstantiate(Goal goal) {
        ifInsts = ImmutableSLList.<PosInOccurrence>nil();
        simplifiedTerm = Optional.empty();
        complete = false;

        final Services services = goal.proof().getServices();
        final TermBuilder tb = services.getTermBuilder();

        final List<Term> elementaries = MergeRuleUtils.getElementaryUpdates(
                UpdateApplication.getUpdate(posInOccurrence().subTerm()), false, tb);

        List<Term> sorted = new ArrayList<>(elementaries);

        for (final Term abstrUpdTerm : elementaries.stream()
                .filter(t -> t.op() instanceof AbstractUpdate).collect(Collectors.toList())) {
            // Elements before the abstract update:
            // - dependent ones which did not originally occur later
            // - independent ones dominated by another update
            // - independent ASs that are lexicographically smaller
            final List<Term> beforeList = new ArrayList<>();

            // Elements before the abstract update:
            // - independent ones
            // - dependent ones that originally occurred later
            final List<Term> afterList = new ArrayList<>();

            final int abstrUpdTermIdx = sorted.indexOf(abstrUpdTerm);

            Outer: for (int i = 0; i < abstrUpdTermIdx; i++) {
                final Term otherUpdTerm = sorted.get(i);

                if (independent(abstrUpdTerm, otherUpdTerm, goal, services)) {
                    if (otherUpdTerm.op() instanceof AbstractUpdate
                            && ((AbstractUpdate) otherUpdTerm.op())
                                    .getAbstractPlaceholderStatement().getId()
                                    .compareTo(((AbstractUpdate) abstrUpdTerm.op())
                                            .getAbstractPlaceholderStatement().getId()) <= 0) {
                        beforeList.add(otherUpdTerm);
                    } else {
                        // Check domination by other update
                        for (int j = i + 1; j < abstrUpdTermIdx; j++) {
                            if (!independent(otherUpdTerm, sorted.get(j), goal, services)) {
                                beforeList.add(otherUpdTerm);
                                continue Outer;
                            }
                        }
                        
                        afterList.add(otherUpdTerm);
                    }
                } else {
                    beforeList.add(otherUpdTerm);
                }
            }

            for (int i = abstrUpdTermIdx + 1; i < sorted.size(); i++) {
                afterList.add(sorted.get(i));
            }

            sorted = new ArrayList<>(beforeList);
            sorted.add(abstrUpdTerm);
            sorted.addAll(afterList);
        }

        if (sorted.equals(elementaries)) {
            ifInsts = ImmutableSLList.<PosInOccurrence>nil();
        } else {
            complete = true;
            simplifiedTerm = Optional.of(tb.apply(
                    tb.parallel(sorted.stream().collect(ImmutableSLList.toImmutableList())),
                    UpdateApplication.getTarget(posInOccurrence().subTerm())));
        }

        return this;
    }

    // ///////////////////////////////////////////////// //
    // //////////////// PRIVATE METHODS //////////////// //
    // ///////////////////////////////////////////////// //

    protected boolean independent(final Term upd1, final Term upd2, final Goal goal,
            final Services services) {
        final List<AbstractUpdateLoc> assignablesLeft = //
                getAssignablesFromElementaryUpdate(upd2, services);
        final List<AbstractUpdateLoc> assignablesRight = //
                getAssignablesFromElementaryUpdate(upd1, services);

        for (final AbstractUpdateLoc leftAssignable : assignablesLeft) {
            // Disjointness is commutative, so this direction suffices.
            if (isRelevant(leftAssignable, assignablesRight, goal, services)) {
                return false;
            }
        }

        return true;
    }

    /**
     * Extracts the assignables from primitive update terms (i.e., empty update,
     * elementary concrete update, or abstract update).
     * 
     * @param updateTerm The update {@link Term} from which to extract.
     * @param services   The {@link Services} object.
     * @return The extracted {@link AbstractUpdateLoc}s.
     */
    private static List<AbstractUpdateLoc> //
            getAssignablesFromElementaryUpdate(final Term updateTerm, Services services) {
        final List<AbstractUpdateLoc> assignables = new ArrayList<>();

        if (updateTerm.op() == UpdateJunctor.SKIP) {
            // Don't do anything
        } else if (updateTerm.op() instanceof ElementaryUpdate) {
            assignables.add( //
                    new PVLoc((LocationVariable) ((ElementaryUpdate) updateTerm.op()).lhs()));
        } else if (updateTerm.op() instanceof AbstractUpdate) {
            ((AbstractUpdate) updateTerm.op()).getAllAssignables().stream()
                    .map(AbstractExecutionUtils::unwrapHasTo).forEach(assignables::add);
        } else {
            throw new IllegalArgumentException("Unexpected operator: " + updateTerm.op());
        }

        return assignables;
    }

    /**
     * Checks whether the given location is relevant w.r.t. the given set of
     * relevant locations.
     * 
     * <p>
     * This method is the significant difference to
     * {@link DropEffectlessElementariesCondition}, since here, we look for premises
     * about disjointness of locsets.
     * 
     * @param loc                  The {@link AbstractUpdateLoc} to check for
     *                             relevance.
     * @param relevantLocations    The relevant locations.
     * @param overwrittenLocations A set of locations that are overwritten and
     *                             therefore definitely irrelevant.
     * @param goal                 The goal in which the {@link Rule} should be
     *                             applied.
     * @param services             The {@link Services} object.
     * @return true iff the given location is relevant w.r.t. the given set of
     *         relevant locations.
     */
    private boolean isRelevant(final AbstractUpdateLoc loc,
            final List<AbstractUpdateLoc> relevantLocations, final Goal goal, Services services) {
        final ImmutableList<PosInOccurrence> evidence = AbstractExecutionUtils.isRelevant(loc,
                relevantLocations, goal, services);

        if (evidence == null) {
            return true;
        }

        this.ifInsts = this.ifInsts.append(evidence);
        return false;
    }
}
