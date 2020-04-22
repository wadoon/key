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
import de.uka.ilkd.key.logic.op.Operator;
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
    private PosInOccurrence pioToReplace = null;

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

        PosInOccurrence parallelUpdPio = posInOccurrence();
        do {
            parallelUpdPio = parallelUpdPio.up();
        } while (!parallelUpdPio.isTopLevel()
                && parallelUpdPio.up().subTerm().op() == UpdateJunctor.PARALLEL_UPDATE);

        pioToReplace = parallelUpdPio;

        final List<Term> elementaries = MergeRuleUtils
                .getElementaryUpdates(parallelUpdPio.subTerm(), false, tb);

        int abstrUpdPos = elementaries.lastIndexOf(posInOccurrence().subTerm());
        assert abstrUpdPos != -1;

        while (abstrUpdPos > 0) {
            if (canSwap( //
                    elementaries.get(abstrUpdPos - 1), //
                    elementaries.get(abstrUpdPos), //
                    goal, services)) {
                final Term tmp = elementaries.get(abstrUpdPos - 1);
                elementaries.set(abstrUpdPos - 1, elementaries.get(abstrUpdPos));
                elementaries.set(abstrUpdPos, tmp);
                abstrUpdPos--;
                complete = true;
            } else {
                break;
            }
        }

        if (!complete) {
            ifInsts = ImmutableSLList.<PosInOccurrence>nil();
        } else {
            simplifiedTerm = Optional.of(
                    tb.parallel(elementaries.stream().collect(ImmutableSLList.toImmutableList())));
        }

        return this;
    }

    /**
     * @return the pioToReplace
     */
    public PosInOccurrence getPioToReplace() {
        return pioToReplace;
    }

    // ///////////////////////////////////////////////// //
    // //////////////// PRIVATE METHODS //////////////// //
    // ///////////////////////////////////////////////// //

    /**
     * Decides whether the two updates can be swapped. Only possible if
     * lexicographic order of updates is not violated, and the assignables don't
     * interfere (there are no conflicts). As a side effect, {@link #ifInsts} is
     * adapted with used premises in case the updates can be swapped.
     * 
     * @param otherUpdTerm The other update term.
     * @param abstrUpdTerm The abstract update term.
     * @param goal         The context {@link Goal}.
     * @param services     The {@link Services} object.
     * @return true iff the updates can be safely swapped.
     */
    private boolean canSwap(final Term otherUpdTerm, final Term abstrUpdTerm, final Goal goal,
            final Services services) {
        assert abstrUpdTerm.op() instanceof AbstractUpdate;

        /*
         * Can swap if (1) otherUpdTerm is *not* an abstract update with a lexically
         * smaller identifier, and (2) the assignables of the two updates are
         * independent. Note that the "accessibles" are irrelevant, since the update is
         * parallel, so neither update influences the right-hand side of the other.
         */

        final AbstractUpdate abstrUpd = (AbstractUpdate) abstrUpdTerm.op();
        final Operator otherOp = otherUpdTerm.op();

        if (otherOp instanceof AbstractUpdate && //
                ((AbstractUpdate) otherOp).getUpdateName()
                        .compareTo(abstrUpd.getUpdateName()) < 0) {
            return false;
        }

        final List<AbstractUpdateLoc> assignablesLeft = //
                getAssignablesFromElementaryUpdate(otherUpdTerm, services);
        final List<AbstractUpdateLoc> assignablesRight = //
                getAssignablesFromElementaryUpdate(abstrUpdTerm, services);

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
     * @param services The {@link Services} object.
     * @return The extracted {@link AbstractUpdateLoc}s.
     */
    private static List<AbstractUpdateLoc> //
            getAssignablesFromElementaryUpdate(final Term updateTerm, Services services) {
        final List<AbstractUpdateLoc> assignables = new ArrayList<>();

        if (updateTerm.op() == UpdateJunctor.SKIP) {
            // Don't do anything
        } else if (updateTerm.op() instanceof ElementaryUpdate) {
            assignables.add( //
                    new PVLoc((LocationVariable) ((ElementaryUpdate) updateTerm.op()).lhs(), services));
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
