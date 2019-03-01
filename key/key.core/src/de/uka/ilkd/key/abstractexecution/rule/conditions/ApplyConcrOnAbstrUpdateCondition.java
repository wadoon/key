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

package de.uka.ilkd.key.abstractexecution.rule.conditions;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.Queue;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Simplifies an update cascade like
 *
 * <pre>
 *     {x1 := t1 || ... || x2 := t2 || ... || x3 := t3 || ... || x4 := t4 || ...}
 *       {U_P(..., hasTo(x1), ..., x4, ... := ... \cup x2 \cup ... \cup x4 \cup ...)}
 *         phi
 * </pre>
 *
 * to
 *
 * <pre>
 *     {... || x4 := t4 || ...}
 *       {U_P(..., hasTo(x1), ..., x4, ... := ... \cup t2 \cup ... \cup t4 \cup ...)}
 *         {x2 := t2 || x3 := t3}
 *           phi
 * </pre>
 *
 * i.e. applies variable assignments to the accessibles of the abstract update,
 * pushes through elementaries that are not assigned by the abstract update, and
 * drops "have-to" elementaries that are assigned by the abstract update.
 * allLocs receives special handling. Only allowed for phi without a Java block
 * (everything fully evaluated) and an update in sequential normal form.
 *
 * Works also for abstract update concatenations; then, the update is stepwise
 * pushed into the concatenation.
 *
 * TODO (DS, 2019-02-13): Check whether there are problems when dropping the "no
 * Java block"-condition. Was introduced originally due give higher priority to
 * the ApplyAbstrOnConcrUpdateCondition rule. But maybe we don't need it???
 *
 * @author Dominic Steinhoefel
 */
public final class ApplyConcrOnAbstrUpdateCondition
        implements VariableCondition {
    private final UpdateSV u1SV;
    private final UpdateSV u2SV;
    private final SchemaVariable phiSV;
    private final SchemaVariable resultSV;

    public ApplyConcrOnAbstrUpdateCondition(UpdateSV u1SV, UpdateSV u2SV,
            SchemaVariable phiSV, SchemaVariable resultSV) {
        this.u1SV = u1SV;
        this.u2SV = u2SV;
        this.phiSV = phiSV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions mc, Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        final Term concrUpdate = (Term) svInst.getInstantiation(u1SV);
        final Term abstrUpdateTerm = (Term) svInst.getInstantiation(u2SV);
        final Term phi = (Term) svInst.getInstantiation(phiSV);
        final Term result = (Term) svInst.getInstantiation(resultSV);

        if (concrUpdate == null || abstrUpdateTerm == null || phi == null
                || result != null) {
            return mc;
        }

        final TermBuilder tb = services.getTermBuilder();

        if (!MergeRuleUtils.isUpdateNormalForm(concrUpdate)) {
            return null;
        }

        if (phi.containsJavaBlockRecursive()) {
            return null;
        }

        /*
         * The concrete update to apply next to the upcoming abstract one in the
         * queue.
         */
        Term currentConcrUpdate = concrUpdate;
        /*
         * Contains a sequence of concrete and abstract updates. We don't
         * concatenate the abstract ones afterward, this can be done again by
         * the concatenation rules.
         */
        final List<Term> resultingUpdates = new ArrayList<>();
        final Queue<Term> abstrUpdatesToProcess = new LinkedList<>();

        abstrUpdatesToProcess.addAll(AbstractExecutionUtils
                .abstractUpdatesFromConcatenation(abstrUpdateTerm));

        boolean success = false;

        while (!abstrUpdatesToProcess.isEmpty()) {
            final Term currentAbstractUpdate = abstrUpdatesToProcess.poll();
            final PushThroughResult pushThroughRes = pushThroughConcrUpdate(
                    currentConcrUpdate, currentAbstractUpdate, services);

            if (pushThroughRes == null && !success) {
                return null;
            }

            if (pushThroughRes != null) {
                pushThroughRes.remainingConcreteUpdate
                        .ifPresent(resultingUpdates::add);
                success = success
                        || !pushThroughRes.remainingConcreteUpdate.isPresent();
                resultingUpdates.add(pushThroughRes.resultingAbstractUpdate);
            } else {
                resultingUpdates.add(currentConcrUpdate);
                resultingUpdates.add(currentAbstractUpdate);
                currentConcrUpdate = null;
            }

            if (pushThroughRes != null
                    && pushThroughRes.pushedThroughConcreteUpdate.isPresent()) {
                currentConcrUpdate = //
                        pushThroughRes.pushedThroughConcreteUpdate
                                .orElseThrow();
                success = true;
            } else {
                /* Nothing remains to be pushed through, wrap up. */
                resultingUpdates.addAll(abstrUpdatesToProcess);
                currentConcrUpdate = null;
                break;
            }
        }

        if (currentConcrUpdate != null) {
            resultingUpdates.add(currentConcrUpdate);
        }

        final Term newResultInst = tb.apply(resultingUpdates, phi);

        svInst = svInst.add(resultSV, newResultInst, services);
        return mc.setInstantiations(svInst);
    }

    /**
     * Performs the actual "push-through" operation for a concrete update in
     * normal form and a single (i.e., not concatenated) abstract update.
     *
     * @param concrUpdate
     *            The concrete update to push through.
     * @param abstrUpdateTerm
     *            The abstract update on which to apply the concrete one.
     * @param tb
     * @param services
     *            The {@link Services} object.
     * @return The new abstract (first component) and concrete (second
     *         component) update, or null if the operation is not allowed (if
     *         allLocs is in the game...).
     */
    private PushThroughResult pushThroughConcrUpdate(final Term concrUpdate,
            final Term abstrUpdateTerm, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final AbstractUpdate abstrUpd = (AbstractUpdate) abstrUpdateTerm.op();

        Term currentAccessibles = abstrUpdateTerm.sub(0);
        final List<Term> currentRemainingConcrUpdElems = new ArrayList<>();
        final List<Term> currentFollowingConcrUpdElems = new ArrayList<>();

        boolean success = false;

        for (LocationVariable lhs : MergeRuleUtils
                .getUpdateLeftSideLocations(concrUpdate)) {
            final PVLoc lhsLoc = new PVLoc(lhs);
            final Term rhs = //
                    MergeRuleUtils.getUpdateRightSideFor(concrUpdate, lhs);

            // First, substitute in the accessibles
            {
                final Term oldAccessibles = currentAccessibles;
                currentAccessibles = AbstractExecutionUtils.replaceVarInTerm(
                        lhs, rhs, currentAccessibles, services);
                if (!oldAccessibles.equals(currentAccessibles)) {
                    success = true;
                }
            }

            /*
             * We may push through if (1) lhs is not assigned (neither "maybe"
             * nor "has to"), and (2) the abstract update does not assign
             * allLocs.
             */
            final boolean mayPushThrough = !abstrUpd.mayAssign(lhsLoc)
                    && !abstrUpd.assignsAllLocs();

            /*
             * We may drop if (1.1) lhs is assigned as "has to" or (1.2) the
             * abstract update does not assign that variable at all and also not
             * allLocs (because then we push through), and (2) the abstract
             * update does not access allLocs.
             */
            final boolean mayDrop = (abstrUpd.hasToAssign(lhsLoc)
                    || (!abstrUpd.mayAssign(lhsLoc)
                            && !abstrUpd.assignsAllLocs()))
                    && !AbstractExecutionUtils.accessesAllLocs(abstrUpdateTerm,
                            services);

            /*
             * Note that there is a situation where the update may be pushed
             * through, but not dropped (that is, it appears twice in the
             * result): If the lhs is not assigned, but the update accesses
             * allLocs.
             */

            final Term elem = tb.elementary(lhs, rhs);

            if (mayPushThrough) {
                currentFollowingConcrUpdElems.add(elem);
                success = true;
            }

            if (!mayDrop) {
                currentRemainingConcrUpdElems.add(elem);
            } else {
                success = true;
            }
        }

        if (!success) {
            return null;
        }

        final Term newAbstrUpdTerm = tb.abstractUpdate(abstrUpd,
                currentAccessibles);

        final Optional<Term> remainingConcrUpdate = //
                currentRemainingConcrUpdElems.isEmpty() ? Optional.empty()
                        : Optional.of(tb.parallel(
                                currentRemainingConcrUpdElems.stream().collect(
                                        ImmutableSLList.toImmutableList())));
        final Optional<Term> followingConcrUpdate = //
                currentFollowingConcrUpdElems.isEmpty() ? Optional.empty()
                        : Optional.of(tb.parallel(
                                currentFollowingConcrUpdElems.stream().collect(
                                        ImmutableSLList.toImmutableList())));

        return new PushThroughResult(remainingConcrUpdate, newAbstrUpdTerm,
                followingConcrUpdate);
    }

    @Override
    public String toString() {
        return String.format("\\applyConcrOnAbstrUpdate(%s, %s, %s, %s)", //
                u1SV, u2SV, phiSV, resultSV);
    }

    private static class PushThroughResult {
        /**
         * The part of the concrete update that cannot be pushed through because
         * of "maybe" assignables in the abstract update.
         */
        public final Optional<Term> remainingConcreteUpdate;
        /**
         * The resulting abstract update, maybe with replaced right-hand sides.
         */
        public final Term resultingAbstractUpdate;
        /**
         * The pushed-through update.
         */
        public final Optional<Term> pushedThroughConcreteUpdate;

        public PushThroughResult(Optional<Term> remainingConcreteUpdate,
                Term resultingAbstractUpdate,
                Optional<Term> pushedThroughConcreteUpdate) {
            this.remainingConcreteUpdate = remainingConcreteUpdate;
            this.resultingAbstractUpdate = resultingAbstractUpdate;
            this.pushedThroughConcreteUpdate = pushedThroughConcreteUpdate;
        }
    }
}