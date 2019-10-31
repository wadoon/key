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

import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.TermAccessibleLocationsCollector;
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
                        collectLocations(target, services), //
                        new LinkedHashSet<>(), //
                        goal, services //
                ).map( //
                        upd -> tb.apply(upd, target, null));

        if (!maybeResult.isPresent()) {
            ifInsts = ImmutableSLList.<PosInOccurrence>nil();
            return this;
        } else {
            complete = true;
            simplifiedTerm = maybeResult;
            return this;
        }
    }

    // ///////////////////////////////////////////////// //
    // //////////////// PRIVATE METHODS //////////////// //
    // ///////////////////////////////////////////////// //

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

        //@formatter:off
//        final Set<AbstractUpdateLoc> newIrrelevantLocations = relevantLocations.stream()
//                .filter(abstrUpd::hasToAssign)
//                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
//        final Set<AbstractUpdateLoc> newOverwrittenLocations = abstrUpd.getHasToAssignables()
//                .stream()
//                .filter(hasToLoc -> newIrrelevantLocations.stream()
//                        .anyMatch(loc -> hasToLoc.mayAssign(loc, services)))
//                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
        //@formatter:on

        if (abstrUpd.getAllAssignables().stream().noneMatch(
                loc -> isRelevant(loc, relevantLocations, overwrittenLocations, goal, services))) {
            return Optional.of(tb.skip());
        }

        //@formatter:off
//        relevantLocations.removeAll(newIrrelevantLocations);
//        overwrittenLocations.addAll(newOverwrittenLocations);
        //@formatter:on
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
        ImmutableList<PosInOccurrence> localIfInsts = ImmutableSLList.<PosInOccurrence>nil();
        final AbstractUpdateLoc locUnwrapped = AbstractExecutionUtils.unwrapHasTo(loc);

        //@formatter:off
        /*
         * A location l1 (set) is *not* relevant w.r.t. another location l2 (set) if:
         * 
         * 1) l1 is overwritten, or there is no relevant location l2, or
         * 2) l1 is a PVLoc and l2 a different PVLoc, or
         * 3) l1 is not a PVLoc, and l2 is a fresh auxiliary program variable, or
         * 4) l1 is a fresh auxiliary program variable and l2 is an abstract location set, or
         * 5) there is evidence in the proof that l1 and l2 are disjoint.
         * 
         * In all other cases, l1 is relevant w.r.t. l2. It is relevant w.r.t. a set of
         * locations if it is relevant for any location in the set.
         * 
         * Case 4 is because the variable wouldn't be fresh if it was contained by the
         * possible instantiations of any abstract location set.
         */
        //@formatter:on

        if (overwrittenLocations.contains(locUnwrapped) || relevantLocations.isEmpty()) {
            return false;
        }

        final Set<AbstractUpdateLoc> relevantLocsCopy = new LinkedHashSet<>(relevantLocations);
        if (locUnwrapped instanceof PVLoc) {
            // If loc is a PVLoc, we can safely remove all PVLocs that aren't equal.
            relevantLocsCopy.removeIf(ploc -> ploc instanceof PVLoc && !ploc.equals(locUnwrapped));
        } else {
            /*
             * Even if loc is allLocs, the "fresh" locations cannot be meant! We remove
             * them. They only should play a role if loc is a PVLoc.
             */
            relevantLocsCopy.removeIf(ploc -> locIsCreatedFresh(ploc, goal, services));
        }

        // loc has to be disjoint from *all* relevant locations.
        for (final AbstractUpdateLoc relevantLoc : relevantLocsCopy) {
            if ((relevantLoc instanceof AllLocsLoc || relevantLoc instanceof SkolemLoc)
                    && locIsCreatedFresh(locUnwrapped, goal, services)) {
                continue;
            }

            final Optional<PosInOccurrence> maybeIrrelevanceEvidence = //
                    isIrrelevant(locUnwrapped, relevantLoc, goal, services);

            if (maybeIrrelevanceEvidence.isPresent()) {
                localIfInsts = localIfInsts.append(maybeIrrelevanceEvidence.get());
            } else {
                // Not irrelevant for this relevantLoc
                return true;
            }
        }

        this.ifInsts = this.ifInsts.append(localIfInsts);
        return false;
    }

    /**
     * For location variables introduced fresh by KeY, there can be no disjointness
     * assumptions created a-priori. Therefore, this method checks whether the given
     * location variable loc is irrelevant for abstract location sets.
     * 
     * <p>
     * Pure method.
     * 
     * @param loc      The {@link AbstractUpdateLoc} to check.
     * @param goal     The context {@link Goal}.
     * @param services The {@link Services} object.
     * @return true iff loc is irrelevant for Skolem location sets since it is
     *         created fresh by KeY rules.
     */
    private static boolean locIsCreatedFresh(final AbstractUpdateLoc loc, final Goal goal,
            final Services services) {
        if (!(AbstractExecutionUtils.unwrapHasTo(loc) instanceof PVLoc)) {
            return false;
        }

        final LocationVariable locVar = ((PVLoc) AbstractExecutionUtils.unwrapHasTo(loc)).getVar();

        /*
         * Location variables that either are already present in the root sequent, or
         * are not related to the source, are considered fresh. Additionally, there is a
         * freshness flag for special variables like the exc, self and result variables
         * created in operation POs. We consider variables that don't have position
         * information as not related to the source. It would be soundness critical if
         * declarations of variables in the source code were not given position
         * information.
         */
        
        if (locVar.isFreshVariable()) {
            return true;
        }

        final OpCollector opColl = new OpCollector();
        StreamSupport.stream(goal.proof().root().sequent().spliterator(), true)
                .map(SequentFormula::formula).forEach(term -> term.execPostOrder(opColl));
        if (opColl.ops().contains(locVar)) {
            // Location was already present in the root node.
            return false;
        }

        return locVar.getPositionInfo() == PositionInfo.UNDEFINED;
    }

    /**
     * Looks in the antecedent of the given {@link Goal} for a premise asserting
     * that loc and relevantLoc are disjoint. The check is done syntactically for
     * performance reasons, but KeY should bring the disjointness assertions to a
     * normal form of the shape <code>loc1 \cap loc2 = {}</code>, therefore it
     * should be OK. There are no proofs involved.
     * 
     * <p>
     * Pure method.
     * 
     * @param loc         The location to check for relevance.
     * @param relevantLoc A location known to be relevant.
     * @param goal        The context {@link Goal}.
     * @param services    The {@link Services} object.
     * @return An empty {@link Optional} if it could not proven that loc is
     *         <em>not</em> relevant, and a premise proving the irrelevance (i.e.,
     *         disjointness) in the other case.
     */
    public static Optional<PosInOccurrence> isIrrelevant(final AbstractUpdateLoc loc,
            final AbstractUpdateLoc relevantLoc, final Goal goal, final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Term locsetDisjointTerm1 = tb.equals(
                tb.intersect(loc.toTerm(services), relevantLoc.toTerm(services)), tb.empty());
        final Term locsetDisjointTerm2 = tb.equals(
                tb.intersect(relevantLoc.toTerm(services), loc.toTerm(services)), tb.empty());

        for (SequentFormula premise : goal.sequent().antecedent()) {
            final Term premiseFor = premise.formula();
            if (premiseFor.equalsModIrrelevantTermLabels(locsetDisjointTerm1)
                    || premiseFor.equalsModIrrelevantTermLabels(locsetDisjointTerm2)) {
                return Optional.of(new PosInOccurrence(premise, PosInTerm.getTopLevel(), true));
            }
        }

        return Optional.empty();
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
