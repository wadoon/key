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
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateAssgnLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.AllFieldsLocRHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.ArrayLocRHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.ArrayRange;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.FieldLocRHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.heap.HeapLocRHS;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Utility functions for abstract execution.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExecutionUtils {
    /**
     * Computes the sets of assigned-before-used and used-before-assigned operators
     * in the target term. In case of a conflict, i.e. in one subterm an operator is
     * used before assigned and in the other vice versa, used before assigned always
     * wins. The returned pair consists of the assigned-before-used set as first and
     * the used-before-assigned set as second element. The two sets are disjunct.
     *
     * @param target          The term for which to analyze the assigned-before-used
     *                        relationships.
     * @param runtimeInstance An optional runtime instance {@link LocationVariable}
     *                        to normalize self terms (because otherwise, there
     *                        might be different such terms around).
     * @param services        The {@link Services} object.
     * @return (1) assigned-before-used and (2) used-before-assigned operators. Sets
     *         are ordered. May be an empty optional if there is a construct not
     *         (yet) supported, in this case, the condition should not be
     *         applicable.
     */
    public static Optional<Pair<Set<AbstractUpdateAssgnLoc>, Set<AbstractUpdateLoc>>> opsAssignedBeforeUsed(
            Term target, Optional<LocationVariable> runtimeInstance, Services services) {
        final Set<AbstractUpdateAssgnLoc> assignedBeforeUsed = new LinkedHashSet<>();
        final Set<AbstractUpdateLoc> usedBeforeAssigned = new LinkedHashSet<>();

        final Set<AbstractUpdateLoc> locs = AbstractUpdateFactory
                .abstrUpdateLocsFromTermUnsafe(target, runtimeInstance, services);

        if (locs != null) {
            locs.stream().filter(AbstractUpdateLoc.class::isInstance)
                    .map(AbstractUpdateLoc.class::cast).forEach(usedBeforeAssigned::add);
        }

        // Update applications -- those are most interesting
        else if (target.op() == UpdateApplication.UPDATE_APPLICATION) {
            final Term update = target.sub(0);
            final Term updateTarget = target.sub(1);

            // Update in sequential normal form
            if (MergeRuleUtils.isUpdateNormalForm(update)) {
                final List<Term> elems = MergeRuleUtils.getElementaryUpdates(update,
                        services.getTermBuilder());

                for (final Term elem : elems) {
                    assert elem.op() instanceof ElementaryUpdate;
                    assert ((ElementaryUpdate) elem.op()).lhs() instanceof LocationVariable;

                    final UpdateableOperator lhs = //
                            ((ElementaryUpdate) elem.op()).lhs();
                    final AbstractUpdateAssgnLoc lhsLoc = //
                            new PVLoc((LocationVariable) lhs);
                    final Term rhs = elem.sub(0);

                    AbstractUpdateFactory
                            .extractAbstrUpdateLocsFromTerm(rhs, runtimeInstance, services).stream()
                            .filter(AbstractUpdateLoc.class::isInstance)
                            .map(AbstractUpdateLoc.class::cast)
                            .filter(loc -> assignedBeforeUsed.stream()
                                    .noneMatch(assgnLoc -> assgnLoc.mayAssign(loc, services)))
                            .forEach(usedBeforeAssigned::add);

                    if (!usedBeforeAssigned.stream()
                            .anyMatch(loc -> lhsLoc.mayAssign(loc, services))) {
                        assignedBeforeUsed.add(lhsLoc);
                    }
                }
            }

            // Abstract Update
            else if (update.op() instanceof AbstractUpdate) {
                opsHaveToAssignBeforeUsedForAbstrUpd(update, assignedBeforeUsed, usedBeforeAssigned,
                        runtimeInstance, services);
            }

            // Concatenated abstract update
            else if (update.op() == UpdateJunctor.CONCATENATED_UPDATE) {
                final List<Term> abstractUpdateTerms = //
                        abstractUpdatesFromConcatenation(update);
                for (Term abstrUpdTerm : abstractUpdateTerms) {
                    opsHaveToAssignBeforeUsedForAbstrUpd(abstrUpdTerm, assignedBeforeUsed,
                            usedBeforeAssigned, runtimeInstance, services);
                }
            }

            // Something else -- ignore for now, exit (completeness relevant)
            else {
                // Probably a nested application
                return Optional.empty();
            }

            final Pair<Set<AbstractUpdateAssgnLoc>, Set<AbstractUpdateLoc>> subResult = //
                    opsAssignedBeforeUsed(updateTarget, runtimeInstance, services).orElse(null);

            if (subResult == null) {
                return Optional.empty();
            }

            usedBeforeAssigned.addAll(subResult.second.stream()
                    .filter(rhsLoc -> !assignedBeforeUsed.stream()
                            .anyMatch(lhsLoc -> lhsLoc.mayAssign(rhsLoc, services)))
                    .collect(Collectors.toSet()));

            assignedBeforeUsed.addAll(subResult.first.stream()
                    .filter(lhsLoc -> !usedBeforeAssigned.stream()
                            .anyMatch(rhsLoc -> lhsLoc.mayAssign(rhsLoc, services)))
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
                final Pair<Set<AbstractUpdateAssgnLoc>, Set<AbstractUpdateLoc>> subResult = //
                        opsAssignedBeforeUsed(sub, runtimeInstance, services).orElse(null);

                if (subResult == null) {
                    return Optional.empty();
                }

                /* Add all "used before assigned" */
                usedBeforeAssigned.addAll(subResult.second);

                /* Add all "assigned before used" */
                assignedBeforeUsed.addAll(subResult.first);

                /*
                 * Now, remove those from "assigned before used" that are used before assigned.
                 * Take that term as example:
                 *
                 * {U}({x:=y}phi & (psi(x)))
                 *
                 * Here, x should be used before assigned and not assigned before used.
                 * Therefore the removal.
                 */
                assignedBeforeUsed.removeIf(abu -> usedBeforeAssigned.stream()
                        .anyMatch(uba -> abu.mayAssign(uba, services)));
            }
        }

        /*
         * At the end, all operators that are assigned before used should not be in the
         * used before assigned set.
         */
        assert assignedBeforeUsed.stream().noneMatch(
                abu -> usedBeforeAssigned.stream().anyMatch(uba -> abu.mayAssign(uba, services)));

        /* Also vice versa */
        assert usedBeforeAssigned.isEmpty() || usedBeforeAssigned.stream().noneMatch(
                uba -> assignedBeforeUsed.stream().anyMatch(abu -> abu.mayAssign(uba, services)));

        return Optional.of(new Pair<>(assignedBeforeUsed, usedBeforeAssigned));
    }

    /**
     * Calculates for an abstract update which operators in it are "have-to"
     * assigned before used. The "maybe" assignables are ignored! The current use
     * case is to drop assignables in prior abstract updates that are overwritten,
     * which does not have to be the case for "maybes".
     *
     * @param update             The abstract update to check.
     * @param assignedBeforeUsed A set of assigned-before-used operators. Results
     *                           are added to the passed set.
     * @param usedBeforeAssigned A set of used-before-assigned operators. Results
     *                           are added to the passed set.
     * @param runtimeInstance    An optional runtime instance
     *                           {@link LocationVariable} to normalize self terms
     *                           (because otherwise, there might be different such
     *                           terms around).
     * @param services           The {@link Services} object.
     */
    private static void opsHaveToAssignBeforeUsedForAbstrUpd(final Term update,
            final Set<AbstractUpdateAssgnLoc> assignedBeforeUsed,
            final Set<AbstractUpdateLoc> usedBeforeAssigned,
            Optional<LocationVariable> runtimeInstance, Services services) {
        assert update.op() instanceof AbstractUpdate;

        usedBeforeAssigned.addAll(AbstractUpdateFactory
                .extractAbstrUpdateLocsFromTerm(update.sub(0), runtimeInstance, services).stream()
                .filter(AbstractUpdateLoc.class::isInstance)
                .filter(op -> assignedBeforeUsed.stream()
                        .noneMatch(assgn -> assgn.mayAssign(op, services)))
                .map(AbstractUpdateLoc.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>())));

        final AbstractUpdate abstrUpdate = (AbstractUpdate) update.op();
        assignedBeforeUsed.addAll(abstrUpdate.getHasToAssignables().stream()
                .filter(hasToAssgn -> usedBeforeAssigned.stream()
                        .noneMatch(used -> hasToAssgn.mayAssign(used, services)))
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>())));
    }

    /**
     * Extracts the list of abstract updates from a concatenation of such.
     *
     * @param concatenation A concatenation of abstract updates
     *                      <code>U1 ++ U2 ++ ... ++ Un</code>.
     * @return The contained abstract updates of the concatenation in the original
     *         order.
     */
    public static List<Term> abstractUpdatesFromConcatenation(Term concatenation) {
        final List<Term> result = new ArrayList<>();

        if (concatenation.op() instanceof AbstractUpdate) {
            result.add(concatenation);
        } else if (concatenation.op() == UpdateJunctor.CONCATENATED_UPDATE) {
            result.addAll(abstractUpdatesFromConcatenation(concatenation.sub(0)));
            result.addAll(abstractUpdatesFromConcatenation(concatenation.sub(1)));
        } else {
            throw new RuntimeException("Not an abstract update or concatenation: " + concatenation);
        }

        return result;
    }

    /**
     * Returns {@link Term}s of the RHS of an {@link AbstractUpdate} term.
     *
     * @param update The {@link AbstractUpdate} {@link Term} for which to return the
     *               accessibles.
     * @param tb     The {@link TermBuilder}, needed for disassembling the update
     *               {@link Term}.
     * @return All {@link Term}s in the RHS of an {@link AbstractUpdate} term.
     */
    public static Set<Term> getAccessiblesForAbstractUpdate(Term update, TermBuilder tb) {
        assert update.op() instanceof AbstractUpdate;
        assert update.arity() == 1;

        return tb.setUnionToSet(update.sub(0));
    }

    /**
     * Checks whether an {@link AbstractUpdate} accesses the allLocs location set.
     *
     * @param update   The {@link AbstractUpdate} to check.
     * @param services The {@link Services} object (for the {@link LocSetLDT}).
     * @return true iff the {@link AbstractUpdate} accesseaccesses allLocs location
     *         set.
     */
    public static boolean accessesAllLocs(Term update, Services services) {
        final Operator allLocs = services.getTypeConverter().getLocSetLDT().getAllLocs();
        return getAccessiblesForAbstractUpdate(update, services.getTermBuilder()).stream()
                .anyMatch(t -> t.op() == allLocs);
    }

    /**
     * Evaluates whether the given abstract update accesses "abstractly" a given
     * location term. This is done by trying to prove that the specified heap
     * locations are disjoint. If this can be shown, the method returns "false", if
     * not, it returns "true" (which is, so to say, the default value, and
     * represents both "true" and "unknown"). Callers of the method should therefore
     * not induce unsound behavior if this method returns true as a false negative.
     * If the method returns false, on the other hand, it can be taken for granted
     * that there is not relation between the location sets.
     * 
     * @param abstrUpdTerm The abstract update term.
     * @param lhsLoc       The location for which abstract access should be checked.
     * @param services     The {@link Services} object.
     * @return true iff the abstract update accesses abstractly the given location.
     */
    public static boolean accessesAbstractly(Term abstrUpdTerm, AbstractUpdateLoc rhsLoc,
            Services services) {
        final Set<AbstractUpdateLoc> abstrUpdateAccLocs = AbstractUpdateFactory
                .abstrUpdateLocsFromTermSafe(abstrUpdTerm.sub(0), Optional.empty(), services);

        if (abstrUpdateAccLocs.stream().anyMatch(AllLocsLoc.class::isInstance)) {
            return true;
        }

        if (!(rhsLoc instanceof HeapLocRHS)) {
            return false;
        }

        final Term rhsLocTermAsLhsLocTerm = //
                convertHeapLocRHStoLocSetTerm((HeapLocRHS) rhsLoc, services);

        final TermBuilder tb = services.getTermBuilder();

        final Term abstrUpdLocUnionTerm = abstrUpdateAccLocs.stream()
                .filter(HeapLocRHS.class::isInstance).map(HeapLocRHS.class::cast)
                //.map(l -> l.toTerm(services))
                .map(rhs -> convertHeapLocRHStoLocSetTerm(rhs, services))
                .collect(Collectors.reducing(tb.empty(), (t1, t2) -> tb.union(t1, t2)));

        if (abstrUpdLocUnionTerm.equals(tb.empty())) {
            return false;
        }

        final Term disjointTerm = tb.disjoint(rhsLocTermAsLhsLocTerm, abstrUpdLocUnionTerm);

        final boolean provablyDisjoint = //
                MergeRuleUtils.isProvableWithSplitting(disjointTerm, services, 1000);

        if (provablyDisjoint) {
            return false;
        }

        return true;
    }

    private static Term convertHeapLocRHStoLocSetTerm(HeapLocRHS toConvert, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        if (toConvert instanceof ArrayLocRHS) {
            return tb.singleton(((ArrayLocRHS) toConvert).getArray(),
                    tb.arr(((ArrayLocRHS) toConvert).getIndex()));
        } else if (toConvert instanceof FieldLocRHS) {
            final Term objTerm = ((FieldLocRHS) toConvert).getObjTerm();
            final LocationVariable fieldPV = ((FieldLocRHS) toConvert).getFieldPV();
            final Term fieldSymbol = tb.func(heapLDT.getFieldSymbolForPV(fieldPV, services));
            return tb.singleton(objTerm, fieldSymbol);
        } else if (toConvert instanceof ArrayRange || toConvert instanceof AllFieldsLocRHS) {
            // Here, the result is the same.
            return toConvert.toTerm(services);
        }

        return null;
    }

    /**
     * Applies the given update (concrete & in normal form!) to the target. This is
     * done by performing a simple substitution of left-hand sides for right-hand
     * sides, which is unsound if there may be modal operators in the target term.
     * So this method is only to be used in situations where this certainly is not
     * the case.
     * 
     * @param upd      The update to apply.
     * @param target   The target term.
     * @param services The {@link Services} object.
     * @return The term after update application.
     */
    public static Term applyUpdate(Term upd, Term target, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        for (Term elemUpd : MergeRuleUtils.getElementaryUpdates(upd, tb)) {
            target = GenericTermReplacer.replace(target, //
                    t -> t.op() == ((ElementaryUpdate) elemUpd.op()).lhs(), //
                    t -> elemUpd.sub(0), //
                    services);
        }

        return target;

        //@formatter:off
//        final Proof proof = services.getProof();
//
//        final Term termAfterUpdAppl = tb.apply(upd, target);
//        final Function pred = //
//                new Function(new Name("auxiliary-pred"), Sort.FORMULA, termAfterUpdAppl.sort());
//        final Term predTerm = tb.func(pred, termAfterUpdAppl);
//        Term simplTerm;
//        try {
//            simplTerm = MergeRuleUtils.simplify(proof, predTerm, 1000);
//        } catch (ProofInputException e) {
//            return termAfterUpdAppl;
//        }
//
//        return simplTerm.sub(0);
        //@formatter:on
    }

    /**
     * @param updateTerm The term to check.
     * @return true iff the given {@link Term} contains an abstract update.
     */
    public static boolean containsAbstractUpdate(Term updateTerm) {
        final OpCollector opColl = new OpCollector();
        updateTerm.execPostOrder(opColl);
        return opColl.ops().stream().anyMatch(AbstractUpdate.class::isInstance);
    }
}
