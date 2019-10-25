// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateAssgnLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.TermAccessibleLocationsCollector;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Drops effectless elementary updates, effectless assignables in abstract
 * updates or whole effectless abstract updates from update terms. If the target
 * term does not contain abstract updates or abstract program elements (in the
 * sense of Abstract Execution), the behavior of this condition corresponds to
 * the old version only considering concrete updates.
 * 
 * This class realizes a conservative behavior in the presence of abstract
 * location sets. If there are <em>any</em> abstract location sets in the target
 * that are not guaranteed to be overwritten, nothing will be dropped at all
 * (apart from abstract updates strictly assigning <em>nothing</em>). A precise
 * solution would check disjointness of location sets, but that's not the
 * purpose of this class which should not perform any reasoning.
 * 
 * Integration of Abstract Execution was the reason to consider not only the set
 * of relevant variables, but also the set of variables that are guaranteed to
 * be overwritten, since this allows for some degree of precision in the
 * presence of abstract updates or abstract program elements.
 * 
 * @author Dominic Steinhoefel
 * @author (numerous unknown others)
 */
public final class DropEffectlessElementariesCondition implements VariableCondition {
    private final UpdateSV uSV;
    private final SchemaVariable targetSV;
    private final SchemaVariable resultSV;

    public DropEffectlessElementariesCondition(UpdateSV uSV, SchemaVariable targetSV,
            SchemaVariable resultSV) {
        this.uSV = uSV;
        this.targetSV = targetSV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions mc,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final SVInstantiations svInst = mc.getInstantiations();

        final Term update = (Term) svInst.getInstantiation(uSV);
        final Term target = (Term) svInst.getInstantiation(targetSV);
        final Term previousResult = (Term) svInst.getInstantiation(resultSV);

        if (update == null || target == null) {
            return mc;
        }

        final Optional<Term> maybeResult = //
                dropEffectlessElementaries( //
                        update, //
                        target, //
                        collectLocations(target, services), //
                        new LinkedHashSet<>(), //
                        services//
                ).map( //
                        upd -> tb.apply(upd, target, null));

        if (!maybeResult.isPresent()) {
            return null;
        }

        final Term result = maybeResult.get();
        if (previousResult == null) {
            return mc.setInstantiations(svInst.add(resultSV, result, services));
        } else if (previousResult.equals(result)) {
            return mc;
        } else {
            return null;
        }
    }

    /**
     * Collects read locations in the target {@link Term}.
     * 
     * @param target   The {@link Term} from which to collect locations.
     * @param services The {@link Services} object.
     * @return The relevant locations in {@link Term}.
     */
    private static Set<AbstractUpdateLoc> collectLocations(Term target, Services services) {
        final TermAccessibleLocationsCollector collector = //
                new TermAccessibleLocationsCollector(services);
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
     * @param services             The {@link Services} object.
     * @return The simplified update application {@link Term}, or
     *         {@link Optional#empty()}.
     */
    private static Optional<Term> dropEffectlessElementaries(final Term update, final Term target,
            final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateAssgnLoc> overwrittenLocations, final Services services) {

        if (update.op() instanceof ElementaryUpdate) {
            return maybeDropElementaryUpdate(update, target, relevantLocations,
                    overwrittenLocations, services);
        } else if (update.op() instanceof AbstractUpdate) {
            return maybeDropOrSimplifyAbstractUpdate(update, target, relevantLocations,
                    overwrittenLocations, services);
        } else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
            return dropEffectlessElementariesInParallelUpdate( //
                    update, target, relevantLocations, overwrittenLocations, services);
        } else if (update.op() == UpdateApplication.UPDATE_APPLICATION) {
            return dropEffectlessElementariesInUpdateApplication( //
                    update, target, relevantLocations, overwrittenLocations, services);
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
     * @param services             The {@link Services} object.
     * @return The simplified update application {@link Term}, or
     *         {@link Optional#empty()}.
     */
    private static Optional<Term> dropEffectlessElementariesInUpdateApplication(final Term update,
            final Term target, final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateAssgnLoc> overwrittenLocations, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term appliedUpdate = update.sub(0);
        final Term targetUpdate = update.sub(1);

        return dropEffectlessElementaries(targetUpdate, target, relevantLocations,
                overwrittenLocations, services)
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
     * @param services             The {@link Services} object.
     * @return The simplified update application {@link Term}, or
     *         {@link Optional#empty()}.
     */
    private static Optional<Term> dropEffectlessElementariesInParallelUpdate(final Term update,
            final Term target, final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateAssgnLoc> overwrittenLocations, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term sub1 = update.sub(0);
        final Term sub2 = update.sub(1);

        /*
         * First descend to the second sub-update to keep relevantVars in good order.
         */
        final Optional<Term> maybeNewSub1 = //
                dropEffectlessElementaries(sub2, target, relevantLocations, overwrittenLocations,
                        services);
        final Optional<Term> maybeNewSub0 = //
                dropEffectlessElementaries(sub1, target, relevantLocations, overwrittenLocations,
                        services);

        if (!maybeNewSub0.isPresent() && !maybeNewSub1.isPresent()) {
            return Optional.empty();
        }

        return Optional.of( //
                tb.parallel(maybeNewSub0.orElse(sub1), maybeNewSub1.orElse(sub2)));
    }

    /**
     * Returns a SKIP update, a simplified abstract update (less assignables), or an
     * empty optional if no simplification is possible. Like
     * {@link #dropElementary(Term, Term, Set, Services, TermBuilder)}, but for the
     * much more complex setting of an abstract update.
     * 
     * @param update               The abstract update to check.
     * @param target               The target formula, for extracting locations.
     * @param overwrittenLocations A set of locations that are overwritten and
     *                             therefore definitely irrelevant.
     * @param services             The {@link Services} object.
     * @return The simplified update {@link Term}, or {@link Optional#empty()}.
     */
    private static Optional<Term> maybeDropOrSimplifyAbstractUpdate(final Term update,
            final Term target, final Set<AbstractUpdateLoc> relevantLocations,
            Set<AbstractUpdateAssgnLoc> overwrittenLocations, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final AbstractUpdate abstrUpd = (AbstractUpdate) update.op();

        //@formatter:off
        /*
         * Logic:
         * 
         * - All locations that *have to* be assigned by an abstract update are no
         *   longer relevant (and also registered as overwritten).
         * - All assignable locations of an abstract update that are not relevant 
         *   can be removed, leading to a simplified abstract update. 
         * - An abstract update not assigning relevant locations can be dropped.
         */
        //@formatter:on

        final Set<AbstractUpdateLoc> newIrrelevantLocations = relevantLocations.stream()
                .filter(abstrUpd::hasToAssign)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
        final Set<AbstractUpdateAssgnLoc> newOverwrittenLocations = abstrUpd.getHasToAssignables()
                .stream()
                .filter(hasToLoc -> newIrrelevantLocations.stream()
                        .anyMatch(loc -> hasToLoc.mayAssign(loc, services)))
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

        final Set<AbstractUpdateAssgnLoc> assignablesToRetainFromAbstrUpd = abstrUpd
                .getAllAssignables().stream().filter(assgn -> isRelevant(assgn, relevantLocations,
                        overwrittenLocations, services))
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

        Term newAbstractUpdateTerm = null;

        if (assignablesToRetainFromAbstrUpd.isEmpty()) {
            /*
             * We may drop the abstract update, not assigning anything relevant or not
             * overwritten
             */
            newAbstractUpdateTerm = tb.skip();
        } else if (!assignablesToRetainFromAbstrUpd.containsAll(abstrUpd.getAllAssignables())) {
            /* We cannot drop the update, but remove some assignables */
            final AbstractUpdate newAbstrUpd = services.abstractUpdateFactory()
                    .changeAssignables(abstrUpd, assignablesToRetainFromAbstrUpd);
            newAbstractUpdateTerm = tb.abstractUpdate(newAbstrUpd, update.subs());
        }

        relevantLocations.removeAll(newIrrelevantLocations);
        overwrittenLocations.addAll(newOverwrittenLocations);
        return Optional.ofNullable(newAbstractUpdateTerm);
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
     * @param services             The {@link Services} object.
     * @return The simplified update {@link Term}, or {@link Optional#empty()}.
     */
    private static Optional<Term> maybeDropElementaryUpdate(final Term update, final Term target,
            final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateAssgnLoc> overwrittenLocations, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final ElementaryUpdate eu = (ElementaryUpdate) update.op();
        final LocationVariable lhs = (LocationVariable) eu.lhs();
        if (isRelevant(lhs, relevantLocations, overwrittenLocations, services)) {

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
     * @param services             The {@link Services} object.
     * @return true iff the given location is relevant w.r.t. the given set of
     *         relevant locations.
     */
    private static boolean isRelevant(final LocationVariable lv,
            final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateAssgnLoc> overwrittenLocations, Services services) {
        /*
         * NOTE (DS, 2019-10-25): In an older version, we had to perform checks by names
         * of LVs for occurrences in APS specs, since there were those problems with
         * renamings. Keep that in mind if the surface again. It would however be better
         * to avoid such hacks in any case.
         */

        return isRelevant(new PVLoc(lv), relevantLocations, overwrittenLocations, services);
    }

    /**
     * Checks whether the given location is relevant w.r.t. the given set of
     * relevant locations.
     * 
     * @param loc                  The {@link AbstractUpdateAssgnLoc} to check for
     *                             relevance.
     * @param relevantLocations    The relevant locations.
     * @param overwrittenLocations A set of locations that are overwritten and
     *                             therefore definitely irrelevant.
     * @param services             The {@link Services} object.
     * @return true iff the given location is relevant w.r.t. the given set of
     *         relevant locations.
     */
    private static boolean isRelevant(final AbstractUpdateAssgnLoc loc,
            final Set<AbstractUpdateLoc> relevantLocations,
            final Set<AbstractUpdateAssgnLoc> overwrittenLocations, Services services) {
        /*
         * For now, we perform an overapproximation: Whenever there's allLocs or a
         * Skolem location set in the relevant locations set, we say that the location
         * is relevant. For fine-grained and more useful checks, we'd have to check
         * disjointness of loc from the relevant locations.
         */

        return !overwrittenLocations.contains(loc) && (relevantLocations.stream()
                .anyMatch(AllLocsLoc.class::isInstance)
                || relevantLocations.stream().anyMatch(SkolemLoc.class::isInstance)
                || relevantLocations.stream().anyMatch(relLoc -> loc.mayAssign(relLoc, services)));
    }

    /**
     * Adds lv to the given set of locations (as a side effect).
     * 
     * @param lv   The location to add.
     * @param locs The locations.
     */
    private static void addToAssngLocationSet(final LocationVariable lv,
            final Set<AbstractUpdateAssgnLoc> locs) {
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

    @Override
    public String toString() {
        return "\\dropEffectlessElementaries(" + uSV + ", " + targetSV + ", " + resultSV + ")";
    }
}