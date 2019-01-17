// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractUpdate;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Variable condition for (1) dropping assignables of abstract updates that are
 * in the target overwritten before they are read (also works for
 * concatenations) and (2) also dropping abstract updates in a concatenation
 * (only) that only write to locations which are not read afterward.
 *
 * @author Dominic Steinhoefel
 */
public final class DropEffectlessAbstractUpdateElementariesCondition
        implements VariableCondition {
    private final UpdateSV uSV;
    private final SchemaVariable targetSV;
    private final SchemaVariable resultSV;

    public DropEffectlessAbstractUpdateElementariesCondition(UpdateSV uSV,
            SchemaVariable targetSV, SchemaVariable resultSV) {
        this.uSV = uSV;
        this.targetSV = targetSV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions mc, Services services) {
        final SVInstantiations svInst = mc.getInstantiations();
        final Term u = (Term) svInst.getInstantiation(uSV);
        Term target = (Term) svInst.getInstantiation(targetSV);
        final Term origResult = (Term) svInst.getInstantiation(resultSV);
        Term newResult = origResult;

        if (u == null || target == null) {
            return null;
        }

        if (origResult != null) {
            return mc;
        }

        if (target.isRigid()) {
            /*
             * TODO (DS, 2019-01-04): CHECK MATCHING FOR NONRIGID TERMS!
             * Actually, the taclets using this condition only match on nonrigid
             * targets. For some reason, however, this matching does not work
             * (i.e., the taclets are also applied to rigid targets). That
             * shouldn't do any harm, but we have other taclets for these cases.
             * We should in any case check why the matching does not work...
             */
            return null;
        }

        if (target.containsJavaBlockRecursive()) {
            return null;
        }

        if (u.op() == UpdateJunctor.CONCATENATED_UPDATE) {
            final List<Term> origAbstractUpdates = //
                    Collections.unmodifiableList(
                            extractAbstractUpdatesFromConcatenation(u));
            final List<Term> newElementaryAbstractUpdates = //
                    new ArrayList<>(origAbstractUpdates);

            final TermBuilder tb = services.getTermBuilder();
            for (int i = origAbstractUpdates.size() - 1; i >= 0; i--) {
                final Term elementaryAbstrUpd = //
                        origAbstractUpdates.get(i);
                Term newUpdate = Optional
                        .ofNullable(dropEffectlessAbstractUpdateElementaries(
                                elementaryAbstrUpd, target, services))
                        .orElse(elementaryAbstrUpd);

                if (DropEffectlessAbstractUpdateCondition
                        .dropEffectlessAbstractUpdate(newUpdate, target,
                                services)) {
                    /*
                     * Maybe new we can drop the update entirely, if it only
                     * writes things that are never read...
                     */
                    newUpdate = tb.skip();
                }

                newElementaryAbstractUpdates.set(i, newUpdate);
                target = tb.apply(newUpdate, target);
            }

            newResult = tb.concatenated(ImmutableSLList.<Term> nil()
                    .append(newElementaryAbstractUpdates));

            if (newElementaryAbstractUpdates.equals(origAbstractUpdates)) {
                return null;
            }
        }
        else {
            newResult = dropEffectlessAbstractUpdateElementaries( //
                    u, target, services);
        }

        if (newResult == null) {
            return null;
        }

        return mc.setInstantiations(svInst.add(resultSV, newResult, services));
    }

    private static List<Term> extractAbstractUpdatesFromConcatenation(
            Term concatenation) {
        final List<Term> result = new ArrayList<>();

        if (concatenation.op() instanceof AbstractUpdate) {
            result.add(concatenation);
        }
        else {
            for (Term sub : concatenation.subs()) {
                result.addAll(extractAbstractUpdatesFromConcatenation(sub));
            }
        }

        return result;
    }

    private static Term dropEffectlessAbstractUpdateElementaries(Term update,
            Term target, Services services) {
        final AbstractUpdate abstrUpd = (AbstractUpdate) update.op();

        final Set<Operator> opsInAssignable = //
                DropEffectlessAbstractUpdateCondition
                        .collectNullaryOps(abstrUpd.lhs(), services);
        final Term abstrUpdAccessiblesTerm = update.sub(0);

        final Function allLocs = //
                services.getTypeConverter().getLocSetLDT().getAllLocs();
        if (opsInAssignable.contains(allLocs)) {
            /*
             * If an abstract update may change all locations, then it is never
             * effectless. However, we can simplify this to allLocs alone if
             * there are more ops in the assignable (the locset union rules
             * don't apply here since the lhs is built into the operator
             * itself).
             */

            if (opsInAssignable.size() > 1) {
                return services.getTermBuilder().abstractUpdate(
                        abstrUpd.getAbstractPlaceholderStatement(),
                        services.getTermBuilder().allLocs(),
                        abstrUpdAccessiblesTerm);
            }

            return null;
        }

        final Pair<Set<Operator>, Set<Operator>> opsAnalysisResult = //
                opsAssignedBeforeUsed(target, services).orElse(null);

        if (opsAnalysisResult == null) {
            return null;
        }

        final Set<Operator> abstrUpdAccessibles = //
                DropEffectlessAbstractUpdateCondition
                        .collectNullaryOps(abstrUpdAccessiblesTerm, services);

        final Set<Operator> opsAssignedBeforeUsed = opsAnalysisResult.first
                .stream()
                /* We remove the accessibles of the abstract update itself. */
                .filter(op -> !abstrUpdAccessibles.contains(op))
                .collect(Collectors.toSet());

        final Set<Operator> newOpsInAssignable = opsInAssignable.stream()
                .filter(op -> !opsAssignedBeforeUsed.contains(op))
                .collect(Collectors.toSet());

        if (opsInAssignable.stream()
                .noneMatch(op -> !newOpsInAssignable.contains(op))) {
            // No change.
            return null;
        }

        return services.getTermBuilder().abstractUpdate(
                abstrUpd.getAbstractPlaceholderStatement(),
                opsToLocSetUnion(newOpsInAssignable, services),
                abstrUpdAccessiblesTerm);
    }

    /**
     * Transforms a set of operators to a union term. Each operator has to be
     * either a {@link LocationVariable} or a {@link Function} of locset sort.
     *
     * @param ops
     *            The operators for the union term.
     * @param services
     *            The {@link Services} object.
     * @return A union term consisting of the operators (wraps
     *         {@link LocationVariable}s in singletonPV(PV(...)) application.
     */
    private static Term opsToLocSetUnion(Set<Operator> ops, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.union(ops.stream()
                .map(op -> op instanceof LocationVariable
                        ? tb.singletonPV(tb.var((LocationVariable) op))
                        : tb.func((Function) op))
                .collect(Collectors.toList()));
    }

    /**
     * Computes the sets of assigned-before-used and used-before-assigned
     * operators in the target term. In case of a conflict, i.e. in one subterm
     * an operator is used before assigned and in the other vice versa, used
     * before assigned always wins. The returned pair consists of the
     * assigned-before-used set as first and the used-before-assigned set as
     * second element. The two sets are disjunct.
     *
     * @param target
     *            The term for which to analyze the assigned-before-used
     *            relationships.
     * @param services
     *            The {@link Services} object.
     * @return (1) assigned-before-used and (2) used-before-assigned operators.
     *         Sets are ordered. May be an empty optional if there is a
     *         construct not (yet) supported, in this case, the condition should
     *         not be applicable.
     */
    private static Optional<Pair<Set<Operator>, Set<Operator>>> opsAssignedBeforeUsed(
            Term target, Services services) {
        final Set<Operator> assignedBeforeUsed = new LinkedHashSet<>();
        final Set<Operator> usedBeforeAssigned = new LinkedHashSet<>();

        // Skolem location set or location variable
        if (isProcVarOrSkolemLocSet(target, services)) {
            usedBeforeAssigned.add(target.op());
        }

        // Update applications -- those are most interesting
        else if (target.op() == UpdateApplication.UPDATE_APPLICATION) {
            final Term update = target.sub(0);
            final Term updateTarget = target.sub(1);

            // Update in sequential normal form
            if (MergeRuleUtils.isUpdateNormalForm(update)) {
                final List<Term> elems = MergeRuleUtils
                        .getElementaryUpdates(update);

                // Start from the right, because those "win"
                for (int i = elems.size() - 1; i >= 0; i--) {
                    final Term elem = elems.get(i);

                    final UpdateableOperator lhs = //
                            ((ElementaryUpdate) elem.op()).lhs();
                    final Term rhs = elem.sub(0);

                    if (isProcVarOrSkolemLocSet(rhs, services)) {
                        if (!assignedBeforeUsed.contains(rhs.op())) {
                            usedBeforeAssigned.add(rhs.op());
                        }
                    }

                    if (!usedBeforeAssigned.contains(lhs)) {
                        assignedBeforeUsed.add(lhs);
                    }
                }
            }

            // Abstract Update
            else if (update.op() instanceof AbstractUpdate) {
                usedBeforeAssigned.addAll(DropEffectlessAbstractUpdateCondition
                        .collectNullaryOps(update.sub(0), services).stream()
                        .filter(op -> !assignedBeforeUsed.contains(op))
                        .collect(Collectors.toSet()));

                assignedBeforeUsed.addAll(DropEffectlessAbstractUpdateCondition
                        .collectNullaryOps(((AbstractUpdate) update.op()).lhs(),
                                services)
                        .stream().filter(op -> !usedBeforeAssigned.contains(op))
                        .collect(Collectors.toSet()));
            }

            // Something else -- ignore for now, exit (completeness relevant)
            else {
                // Parallel update, concatenated update, nested application
                return Optional.empty();
            }

            final Pair<Set<Operator>, Set<Operator>> subResult = //
                    opsAssignedBeforeUsed(updateTarget, services).orElse(null);

            if (subResult == null) {
                return Optional.empty();
            }

            usedBeforeAssigned.addAll(subResult.second.stream()
                    .filter(op -> !assignedBeforeUsed.contains(op))
                    .collect(Collectors.toSet()));

            assignedBeforeUsed.addAll(subResult.first.stream()
                    .filter(op -> !usedBeforeAssigned.contains(op))
                    .collect(Collectors.toSet()));
        }

        // Any other term
        else {
            for (final Term sub : target.subs()) {
                final Pair<Set<Operator>, Set<Operator>> subResult = //
                        opsAssignedBeforeUsed(sub, services).orElse(null);

                if (subResult == null) {
                    return Optional.empty();
                }

                /* Add all "used before assigned" */
                usedBeforeAssigned.addAll(subResult.second);

                /* Add all "assigned before used" */
                assignedBeforeUsed.addAll(subResult.first);

                /*
                 * Now, remove those from "assigned before used" that are used
                 * before assigned. Take that term as example:
                 *
                 * {U}({x:=y}phi & (psi(x)))
                 *
                 * Here, x should be used before assigned and not assigned
                 * before used. Therefore the removal.
                 */
                assignedBeforeUsed.removeAll(usedBeforeAssigned);
            }
        }

        /*
         * At the end, all operators that are assigned before used should not be
         * in the used before assigned set.
         */
        final boolean test1 = assignedBeforeUsed.stream()
                .noneMatch(usedBeforeAssigned::contains);
        assert test1;
        // assert assignedBeforeUsed.stream()
        // .noneMatch(usedBeforeAssigned::contains);

        /* Also vice versa */
        assert usedBeforeAssigned.isEmpty() || usedBeforeAssigned.stream()
                .noneMatch(assignedBeforeUsed::contains);

        return Optional.of(new Pair<>(assignedBeforeUsed, usedBeforeAssigned));
    }

    private static boolean isProcVarOrSkolemLocSet(Term term,
            Services services) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final Operator op = term.op();
        return term.arity() == 0 && (op instanceof LocationVariable //
                || (op instanceof Function
                        && ((Function) op).sort() == locSetLDT.targetSort()));
    }

    @Override
    public String toString() {
        return String.format(
                "\\dropEffectlessAbstractUpdateElementaries(%s, %s)", uSV,
                targetSV, resultSV);
    }

}