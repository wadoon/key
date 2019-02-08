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

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.AbstractExecutionUtils;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Simplifies an update cascade like
 *
 * <pre>
 *     {x1 := t1 || ... || x2 := y || ... || x3 := t3 || ...}
 *       {U_P(..., x1, ... := ... \cup x2 \cup ...)}
 *         phi
 * </pre>
 *
 * to
 *
 * <pre>
 *     {U_P(..., x1, ... := ... \cup y \cup ...)}
 *       {x2 := y || x3 := t3}
 *         phi
 * </pre>
 *
 * i.e. applies variable assignments to the accessibles of the abstract update,
 * pushes through elementaries that are not assigned by the abstract update, and
 * drops elementaries that are assigned by the abstract update. Only allowed for
 * phi without a Java block (everything fully evaluated) and an update in
 * sequential normal form.
 *
 * Works also for abstract udpate concatenations; then, the update is stepwise
 * pushed into the concatenation.
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

        Term currentConcrUpdate = concrUpdate;
        List<Term> processedAbstrUpdates = new ArrayList<>();
        Queue<Term> abstrUpdatesToProcess = new LinkedList<>();

        abstrUpdatesToProcess.addAll(AbstractExecutionUtils
                .abstractUpdatesFromConcatenation(abstrUpdateTerm));

        while (!abstrUpdatesToProcess.isEmpty()) {
            final Term currentAbstractUpdate = abstrUpdatesToProcess.poll();
            final Pair<Term, Term> newAbstrAndConcrUpd = pushThroughConcrUpdate(
                    currentConcrUpdate, currentAbstractUpdate, tb, services);

            if (newAbstrAndConcrUpd == null) {
                /*
                 * NOTE (DS, 2019-02-08): We could also consider to break and
                 * leave a concrete update in the middle of a concatenation, but
                 * that was not desired when implementing this.
                 */
                return null;
            }

            processedAbstrUpdates.add(newAbstrAndConcrUpd.first);
            currentConcrUpdate = newAbstrAndConcrUpd.second;
        }

        final Term newResultInst = //
                tb.apply(tb.concatenated(processedAbstrUpdates),
                        tb.apply(currentConcrUpdate, phi));

        svInst = svInst.add(resultSV, newResultInst, services);
        return mc.setInstantiations(svInst);
    }

    /**
     * Performs the actual "push-through" operation for a concrete update in
     * normal form and a single (i.e., not concatenated) abstract update.
     *
     * @param concrUpdate
     *            The concrete update to push through.
     * @param abstrUpdate
     *            The abstract update on which to apply the concrete one.
     * @param tb
     * @param services
     *            The {@link Services} object.
     * @return The new abstract (first component) and concrete (second
     *         component) update, or null if the operation is not allowed (if
     *         allLocs is in the game...).
     */
    private Pair<Term, Term> pushThroughConcrUpdate(final Term concrUpdate,
            final Term abstrUpdate, final TermBuilder tb, Services services) {
        final AbstractUpdate abstrUpd = (AbstractUpdate) abstrUpdate.op();

        if (AbstractExecutionUtils.assignsAllLocs(abstrUpd, services)
                || AbstractExecutionUtils.accessesAllLocs(abstrUpdate,
                        services)) {
            /*
             * For this case (U(allLocs:=...) / U(...:=allLocs)) we won't not do
             * anything. The abstract update depends on everything changed in
             * the concrete update...
             */
            return null;
        }

        final Set<LocationVariable> assgnVarsOfAbstrUpd = AbstractExecutionUtils
                .collectNullaryPVsOrSkLocSets(abstrUpd.lhs(), services).stream()
                .filter(LocationVariable.class::isInstance)
                .map(LocationVariable.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

        Term currentAccessibles = abstrUpdate.sub(0);
        final List<Term> currentNewConcrUpdElems = new ArrayList<>();

        for (LocationVariable lhs : MergeRuleUtils
                .getUpdateLeftSideLocations(concrUpdate)) {
            final Term rhs = MergeRuleUtils.getUpdateRightSideFor(concrUpdate,
                    lhs);

            // First, substitute in the accessibles
            currentAccessibles = ApplyAbstrOnConcrUpdateCondition
                    .replaceVarInTerm(lhs, rhs, currentAccessibles, services);

            // Decide whether to push through
            if (!assgnVarsOfAbstrUpd.contains(lhs)) {
                // Push through
                currentNewConcrUpdElems.add(tb.elementary(lhs, rhs));
            }
        }

        final Term newAbstrUpdTerm = tb.abstractUpdate(
                abstrUpd.getAbstractPlaceholderStatement(), abstrUpd.lhs(),
                currentAccessibles);

        final Term newConcrUpdate = tb.parallel(currentNewConcrUpdElems.stream()
                .collect(ImmutableSLList.toImmutableList()));

        return new Pair<>(newAbstrUpdTerm, newConcrUpdate);
    }

    @Override
    public String toString() {
        return String.format("\\applyConcrOnAbstrUpdate(%s, %s, %s, %s)", //
                u1SV, u2SV, phiSV, resultSV);
    }
}