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

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.IrrelevantAssignable;
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
import de.uka.ilkd.key.proof.TermAccessibleLocationsCollector;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.rule.conditions.DropEffectlessElementariesCondition;

/**
 * {@link RuleApp} for the {@link SimplifyUpdatesAbstractRule}.
 * 
 * @author Dominic Steinhoefel
 */
public class SimplifyUpdatesAbstractRuleApp extends DefaultBuiltInRuleApp {
    private ImmutableList<PosInOccurrence> ifInsts = ImmutableSLList.<PosInOccurrence>nil();
    private boolean complete = false;
    private Optional<Term> simplifiedTerm = Optional.empty();

    // ///////////////////////////////////////////////// //
    // //////////////// PUBLIC INTERFACE /////////////// //
    // ///////////////////////////////////////////////// //

    public SimplifyUpdatesAbstractRuleApp(BuiltInRule builtInRule, PosInOccurrence pio) {
        super(builtInRule, pio);
    }

    public SimplifyUpdatesAbstractRuleApp(BuiltInRule builtInRule, PosInOccurrence pio,
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
    public SimplifyUpdatesAbstractRuleApp tryToInstantiate(Goal goal) {
        ifInsts = ImmutableSLList.<PosInOccurrence>nil();
        simplifiedTerm = Optional.empty();
        complete = false;

        final Services services = goal.proof().getServices();
        final TermBuilder tb = services.getTermBuilder();

        final Term t = posInOccurrence().subTerm();
        final Term update = UpdateApplication.getUpdate(t);
        final Term target = UpdateApplication.getTarget(t);

        final Optional<Term> maybeResult = //
                dropEffectlessElementaries( //
                        update, //
                        target, //
                        collectLocations(target, goal.getLocalSpecificationRepository(), services), //
                        new LinkedHashSet<>(), //
                        goal, services //
                ).map( //
                        upd -> tb.apply(upd, target, null));

        if (!maybeResult.isPresent()) {
            ifInsts = ImmutableSLList.<PosInOccurrence>nil();
        } else {
            complete = true;
            simplifiedTerm = maybeResult;
        }

        return this;
    }

    // ///////////////////////////////////////////////// //
    // //////////////// PRIVATE METHODS //////////////// //
    // ///////////////////////////////////////////////// //

    /**
     * Collects read locations in the target {@link Term}.
     * 
     * @param target        The {@link Term} from which to collect locations.
     * @param localSpecRepo TODO
     * @param services      The {@link Services} object.
     * @return The relevant locations in {@link Term}.
     */
    private static Set<AbstractUpdateLoc> collectLocations(Term target,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        final TermAccessibleLocationsCollector collector = //
                new TermAccessibleLocationsCollector(localSpecRepo, services);
        target.execPostOrder(collector);
        return collector.locations();
    }

    /**
     * Returns, if possible, a simplified update <code>update'</code> such that
     * <code>{update'}target</code> is equivalent to <code>{update}target</code>.
     * Uses the locations in relevantVars to decide what to drop in the
     * simplification step (updates not assigning relevant variables can be
     * dropped). Returns {@link Optional#empty()} if simplification is not possible.
     * 
     * @param update               The update to simplify.
     * @param target               The target formula, for extracting locations.
     * @param overwrittenLocations A set of locations that are overwritten and
     *                             therefore definitely irrelevant.
     * @param goal                 The goal in which the {@link Rule} should be
     *                             applied.
     * @param services             The {@link Services} object.
     * @return The simplified update application {@link Term}, or
     *         {@link Optional#empty()}.
     */
    private Optional<Term> dropEffectlessElementaries(final Term update, final Term target,
            final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateLoc> overwrittenLocations, final Goal goal,
            final Services services) {

        if (update.op() instanceof ElementaryUpdate) {
            return maybeDropElementaryUpdate(update, target, relevantLocations,
                    overwrittenLocations, goal, services);
        } else if (update.op() instanceof AbstractUpdate) {
            return maybeDropAbstractUpdate(update, target, relevantLocations, overwrittenLocations,
                    goal, services);
        } else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
            return descendInParallelUpdate( //
                    update, target, relevantLocations, overwrittenLocations, goal, services);
        } else if (update.op() == UpdateApplication.UPDATE_APPLICATION) {
            return descendInUpdateApplication( //
                    update, target, relevantLocations, overwrittenLocations, goal, services);
        } else {
            // Unknown operator.
            return Optional.empty();
        }
    }

    /**
     * Returns, if possible, a simplified update <code>update'</code> such that
     * <code>{update'}target</code> is equivalent to <code>{update}target</code>,
     * for the case that update is an update application. Uses the locations in
     * relevantVars to decide what to drop in the simplification step (updates not
     * assigning relevant variables can be dropped). Returns
     * {@link Optional#empty()} if simplification is not possible.
     * 
     * @param update               The update application update to simplify.
     * @param target               The target formula, for extracting locations.
     * @param overwrittenLocations A set of locations that are overwritten and
     *                             therefore definitely irrelevant.
     * @param goal                 The goal in which the {@link Rule} should be
     *                             applied.
     * @param services             The {@link Services} object.
     * @return The simplified update application {@link Term}, or
     *         {@link Optional#empty()}.
     */
    private Optional<Term> descendInUpdateApplication(final Term update, final Term target,
            final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateLoc> overwrittenLocations, final Goal goal,
            final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term appliedUpdate = update.sub(0);
        final Term targetUpdate = update.sub(1);

        return dropEffectlessElementaries(targetUpdate, target, relevantLocations,
                overwrittenLocations, goal, services)
                        .map(newSub -> tb.apply(appliedUpdate, newSub, null));
    }

    /**
     * Returns, if possible, a simplified update <code>update'</code> such that
     * <code>{update'}target</code> is equivalent to <code>{update}target</code>,
     * for the case that update is a parallel update. Uses the locations in
     * relevantVars to decide what to drop in the simplification step (updates not
     * assigning relevant variables can be dropped). Returns
     * {@link Optional#empty()} if simplification is not possible.
     * 
     * @param update               The parallel update to simplify.
     * @param target               The target formula, for extracting locations.
     * @param overwrittenLocations A set of locations that are overwritten and
     *                             therefore definitely irrelevant.
     * @param goal                 The goal in which the {@link Rule} should be
     *                             applied.
     * @param services             The {@link Services} object.
     * @return The simplified update application {@link Term}, or
     *         {@link Optional#empty()}.
     */
    private Optional<Term> descendInParallelUpdate(final Term update, final Term target,
            final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateLoc> overwrittenLocations, final Goal goal,
            final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term sub1 = update.sub(0);
        final Term sub2 = update.sub(1);

        /*
         * First descend to the second sub-update to keep relevantVars in good order.
         */
        final Optional<Term> maybeNewSub2 = //
                dropEffectlessElementaries(sub2, target, relevantLocations, overwrittenLocations,
                        goal, services);
        final Optional<Term> maybeNewSub1 = //
                dropEffectlessElementaries(sub1, target, relevantLocations, overwrittenLocations,
                        goal, services);

        if (!maybeNewSub1.isPresent() && !maybeNewSub2.isPresent()) {
            return Optional.empty();
        }

        return Optional.of( //
                tb.parallel(maybeNewSub1.orElse(sub1), maybeNewSub2.orElse(sub2)));
    }

    /**
     * Returns a SKIP update or an empty optional if dropping the abstract update is
     * not possible. Abstract updates cannot be "simplified", either they're
     * relevant or not.
     * 
     * Like {@link #dropElementary(Term, Term, Set, Services, TermBuilder)}, but for
     * the much more complex setting of an abstract update.
     * 
     * @param update               The abstract update to check.
     * @param target               The target formula, for extracting locations.
     * @param overwrittenLocations A set of locations that are overwritten and
     *                             therefore definitely irrelevant.
     * @param goal                 The goal in which the {@link Rule} should be
     *                             applied.
     * @param services             The {@link Services} object.
     * @return The simplified update {@link Term}, or {@link Optional#empty()}.
     */
    private Optional<Term> maybeDropAbstractUpdate(final Term update, final Term target,
            final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateLoc> overwrittenLocations, final Goal goal,
            final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final AbstractUpdate abstrUpd = (AbstractUpdate) update.op();

        if (abstrUpd.assignsNothing()) {
            // Rare special case
            return Optional.of(tb.skip());
        }

        //@formatter:off
        /*
         * Logic:
         * 
         * - All locations that *have to* be assigned by an abstract update are no
         *   longer relevant (and also registered as overwritten).
         * - An abstract update not assigning relevant locations can be dropped.
         */
        //@formatter:on

        final Map<AbstractUpdateLoc, AbstractUpdateLoc> assgnReplMap = new LinkedHashMap<>();
        boolean allLocsIrrelevant = true;
        int i = -1;
        for (final AbstractUpdateLoc assgn : abstrUpd.getAllAssignables()) {
            i++;
            if (assgn instanceof IrrelevantAssignable) {
                continue;
            }

            if (isRelevant(assgn, relevantLocations, overwrittenLocations, goal, services)) {
                allLocsIrrelevant = false;

                if (assgn instanceof HasToLoc) {
                    final AbstractUpdateLoc unwrappedLoc = //
                            AbstractExecutionUtils.unwrapHasTo(assgn);
                    relevantLocations.remove(unwrappedLoc);
                    overwrittenLocations.add(unwrappedLoc);
                }
            } else {
                assgnReplMap.put(assgn, new IrrelevantAssignable(i, assgn.sort()));
            }
        }

        if (allLocsIrrelevant) {
            return Optional.of(tb.skip());
        }

        if (!assgnReplMap.isEmpty()) {
            return Optional.of(tb.changeAbstractUpdateAssignables(update, assgnReplMap));
        }

        return Optional.empty();
    }

    /**
     * Returns either a SKIP update if the elementary update <code>update</code> can
     * be dropped (which is the case if it assigns a variable that is not relevant),
     * or an empty optional if it assigns a relevant variable. In that case, as a
     * <strong>side effect</strong>, that variable is removed from the set of
     * relevant variables and added to the set of overwritten locations, since it's
     * overwritten.
     * 
     * @param update               The elementary update to check.
     * @param target               The target formula, for extracting locations.
     * @param overwrittenLocations A set of locations that are overwritten and
     *                             therefore definitely irrelevant.
     * @param goal                 The goal in which the {@link Rule} should be
     *                             applied.
     * @param services             The {@link Services} object.
     * @return The simplified update {@link Term}, or {@link Optional#empty()}.
     */
    private Optional<Term> maybeDropElementaryUpdate(final Term update, final Term target,
            final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateLoc> overwrittenLocations, final Goal goal,
            final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final ElementaryUpdate eu = (ElementaryUpdate) update.op();
        final LocationVariable lhs = (LocationVariable) eu.lhs();

        if (isRelevant(lhs, relevantLocations, overwrittenLocations, goal, services)) {

            removeFromLocationSet(lhs, relevantLocations); // SIDE EFFECT!
            addToAssngLocationSet(lhs, overwrittenLocations); // SIDE EFFECT!

            /* NOTE: Cannot discard updates of the form x:=x, see bug #1269 (MU, CS) */
            return Optional.empty();
        } else {
            return Optional.of(tb.skip());
        }
    }

    /**
     * Checks whether the given location is relevant w.r.t. the given set of
     * relevant locations.
     * 
     * @param lv                   The {@link LocationVariable} to check for
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
    private boolean isRelevant(final LocationVariable lv,
            final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateLoc> overwrittenLocations, final Goal goal, Services services) {
        /*
         * NOTE (DS, 2019-10-25): In an older version, we had to perform checks by names
         * of LVs for occurrences in APS specs, since there were those problems with
         * renamings. Keep that in mind if the surface again. It would however be better
         * to avoid such hacks in any case.
         */

        return isRelevant(new PVLoc(lv), relevantLocations, overwrittenLocations, goal, services);
    }

    /**
     * Checks whether the given location is relevant w.r.t. the given set of
     * relevant locations. Changes {@link #ifInsts} in case that evicence was used
     * in a successful irrelevance "proof".
     * 
     * <p>
     * See
     * {@link AbstractExecutionUtils#isRelevant(AbstractUpdateLoc, Set, Set, Goal, Services)}.
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
            final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateLoc> overwrittenLocations, final Goal goal, Services services) {
        ImmutableList<PosInOccurrence> evidence = AbstractExecutionUtils.isRelevant(loc,
                relevantLocations, overwrittenLocations, goal, services);

        if (evidence == null) {
            return true;
        }

        this.ifInsts = this.ifInsts.append(evidence);
        return false;
    }

    /**
     * Adds lv to the given set of locations (as a side effect).
     * 
     * @param lv   The location to add.
     * @param locs The locations.
     */
    private static void addToAssngLocationSet(final LocationVariable lv,
            final Set<AbstractUpdateLoc> locs) {
        locs.add(new PVLoc(lv));
    }

    /**
     * Removes lv from the given set of locations (as a side effect).
     * 
     * @param lv   The location to remove.
     * @param locs The locations.
     */
    private static void removeFromLocationSet(final LocationVariable lv,
            final Set<AbstractUpdateLoc> locs) {
        locs.remove(new PVLoc(lv));
    }
}
