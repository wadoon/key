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
package de.uka.ilkd.key.abstractexecution.util;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateUpdatableLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Utility functions for abstract execution.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExecutionUtils {
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
     * @param ec
     *            The {@link ExecutionContext}, for handling fields.
     * @param services
     *            The {@link Services} object.
     * @return (1) assigned-before-used and (2) used-before-assigned operators.
     *         Sets are ordered. May be an empty optional if there is a
     *         construct not (yet) supported, in this case, the condition should
     *         not be applicable.
     */
    public static Optional<Pair<Set<AbstrUpdateUpdatableLoc>, Set<AbstrUpdateUpdatableLoc>>> opsAssignedBeforeUsed(
            Term target, ExecutionContext ec, Services services) {
        final Set<AbstrUpdateUpdatableLoc> assignedBeforeUsed = new LinkedHashSet<>();
        final Set<AbstrUpdateUpdatableLoc> usedBeforeAssigned = new LinkedHashSet<>();
        final AbstractUpdateFactory factory = services.abstractUpdateFactory();

        Optional<AbstractUpdateLoc> loc = factory
                .tryExtractAbstrUpdateLocFromTerm(target, ec, services);
        if (loc.isPresent() && loc.get() instanceof AbstrUpdateUpdatableLoc) {
            usedBeforeAssigned.add((AbstrUpdateUpdatableLoc) loc.get());
        }

        // Update applications -- those are most interesting
        else if (target.op() == UpdateApplication.UPDATE_APPLICATION) {
            final Term update = target.sub(0);
            final Term updateTarget = target.sub(1);

            // Update in sequential normal form
            if (MergeRuleUtils.isUpdateNormalForm(update)) {
                final List<Term> elems = MergeRuleUtils
                        .getElementaryUpdates(update);

                for (final Term elem : elems) {
                    final AbstrUpdateUpdatableLoc lhs = new PVLoc(
                            (LocationVariable) ((ElementaryUpdate) elem.op())
                                    .lhs());
                    final Term rhs = elem.sub(0);
                    loc = factory.tryExtractAbstrUpdateLocFromTerm( //
                            rhs, ec, services);
                    if (loc.isPresent()
                            && loc.get() instanceof AbstrUpdateUpdatableLoc) {
                        if (!assignedBeforeUsed.contains(loc.get())) {
                            usedBeforeAssigned
                                    .add((AbstrUpdateUpdatableLoc) loc.get());
                        }
                    }

                    if (!usedBeforeAssigned.contains(lhs)) {
                        assignedBeforeUsed.add(lhs);
                    }
                }
            }

            // Abstract Update
            else if (update.op() instanceof AbstractUpdate) {
                opsHaveToAssignBeforeUsedForAbstrUpd(update, assignedBeforeUsed,
                        usedBeforeAssigned, ec, services);
            }

            // Concatenated abstract update
            else if (update.op() == UpdateJunctor.CONCATENATED_UPDATE) {
                final List<Term> abstractUpdateTerms = //
                        abstractUpdatesFromConcatenation(update);
                for (Term abstrUpdTerm : abstractUpdateTerms) {
                    opsHaveToAssignBeforeUsedForAbstrUpd(abstrUpdTerm,
                            assignedBeforeUsed, usedBeforeAssigned, ec,
                            services);
                }
            }

            // Something else -- ignore for now, exit (completeness relevant)
            else {
                // Probably a nested application
                return Optional.empty();
            }

            final Pair<Set<AbstrUpdateUpdatableLoc>, Set<AbstrUpdateUpdatableLoc>> subResult = //
                    opsAssignedBeforeUsed(updateTarget, ec, services)
                            .orElse(null);

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

        else if (target.op() instanceof Modality) {
            /*
             * TODO (DS, 2019-02-01): Use some existing collector for programs.
             */
            return Optional.empty();
        }

        // Any other term
        else {
            for (final Term sub : target.subs()) {
                final Pair<Set<AbstrUpdateUpdatableLoc>, Set<AbstrUpdateUpdatableLoc>> subResult = //
                        opsAssignedBeforeUsed(sub, ec, services).orElse(null);

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
        assert assignedBeforeUsed.stream()
                .noneMatch(usedBeforeAssigned::contains);

        /* Also vice versa */
        assert usedBeforeAssigned.isEmpty() || usedBeforeAssigned.stream()
                .noneMatch(assignedBeforeUsed::contains);

        return Optional.of(new Pair<>(assignedBeforeUsed, usedBeforeAssigned));
    }

    /**
     * Calculates for an abstract update which operators in it are "have-to"
     * assigned before used. The "maybe" assignables are ignored! The current
     * use case is to drop assignables in prior abstract updates that are
     * overwritten, which does not have to be the case for "maybes".
     *
     * @param update
     *            The abstract update to check.
     * @param assignedBeforeUsed
     *            A set of assigned-before-used operators. Results are added to
     *            the passed set.
     * @param usedBeforeAssigned
     *            A set of used-before-assigned operators. Results are added to
     *            the passed set.
     * @param ec
     *            The {@link ExecutionContext} for handling fields.
     * @param services
     *            The {@link Services} object.
     */
    private static void opsHaveToAssignBeforeUsedForAbstrUpd(final Term update,
            final Set<AbstrUpdateUpdatableLoc> assignedBeforeUsed,
            final Set<AbstrUpdateUpdatableLoc> usedBeforeAssigned,
            ExecutionContext ec, Services services) {
        assert update.op() instanceof AbstractUpdate;

        usedBeforeAssigned.addAll(AbstractUpdateFactory
                .abstractUpdateLocsFromUnionTerm(update.sub(0), ec, services)
                .stream().filter(AbstrUpdateUpdatableLoc.class::isInstance)
                .filter(op -> !assignedBeforeUsed.contains(op))
                .map(AbstrUpdateUpdatableLoc.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>())));

        final AbstractUpdate abstrUpdate = (AbstractUpdate) update.op();
        assignedBeforeUsed.addAll(abstrUpdate.getHasToAssignables().stream()
                .filter(op -> !usedBeforeAssigned.contains(op))
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>())));
    }

    /**
     * Extracts the list of abstract updates from a concatenation of such.
     *
     * @param concatenation
     *            A concatenation of abstract updates
     *            <code>U1 ++ U2 ++ ... ++ Un</code>.
     * @return The contained abstract updates of the concatenation in the
     *         original order.
     */
    public static List<Term> abstractUpdatesFromConcatenation(
            Term concatenation) {
        final List<Term> result = new ArrayList<>();

        if (concatenation.op() instanceof AbstractUpdate) {
            result.add(concatenation);
        } else if (concatenation.op() == UpdateJunctor.CONCATENATED_UPDATE) {
            result.addAll(
                    abstractUpdatesFromConcatenation(concatenation.sub(0)));
            result.addAll(
                    abstractUpdatesFromConcatenation(concatenation.sub(1)));
        } else {
            throw new RuntimeException(
                    "Not an abstract update or concatenation: "
                            + concatenation);
        }

        return result;
    }

    /**
     * Returns {@link Term}s of the RHS of an {@link AbstractUpdate} term.
     *
     * @param update
     *            The {@link AbstractUpdate} {@link Term} for which to return
     *            the accessibles.
     * @param tb
     *            The {@link TermBuilder}, needed for disassembling the update
     *            {@link Term}.
     * @return All {@link Term}s in the RHS of an {@link AbstractUpdate} term.
     */
    public static Set<Term> getAccessiblesForAbstractUpdate(Term update,
            TermBuilder tb) {
        assert update.op() instanceof AbstractUpdate;
        assert update.arity() == 1;

        return tb.setUnionToSet(update.sub(0));
    }

    /**
     * Checks whether an {@link AbstractUpdate} accesses the allLocs location
     * set.
     *
     * @param update
     *            The {@link AbstractUpdate} to check.
     * @param services
     *            The {@link Services} object (for the {@link LocSetLDT}).
     * @return true iff the {@link AbstractUpdate} accesseaccesses allLocs
     *         location set.
     */
    public static boolean accessesAllLocs(Term update, Services services) {
        final Operator allLocs = services.getTypeConverter().getLocSetLDT()
                .getAllLocs();
        return getAccessiblesForAbstractUpdate(update,
                services.getTermBuilder()).stream()
                        .anyMatch(t -> t.op() == allLocs);
    }
}
