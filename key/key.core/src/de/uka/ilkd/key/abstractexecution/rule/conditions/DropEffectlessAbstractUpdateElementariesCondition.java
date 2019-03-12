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

package de.uka.ilkd.key.abstractexecution.rule.conditions;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateLHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateRHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateUpdatableLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Pair;

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

//        final Optional<LocationVariable> runtimeInstance = Optional
//                .ofNullable(svInst.getExecutionContext().getRuntimeInstance())
//                .filter(LocationVariable.class::isInstance)
//                .map(LocationVariable.class::cast);
        final Optional<LocationVariable> runtimeInstance = Optional.empty();

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
                final Term newUpdate = Optional
                        .ofNullable(dropEffectlessAbstractUpdateElementaries(
                                elementaryAbstrUpd, target, runtimeInstance, services))
                        .orElse(elementaryAbstrUpd);

                newElementaryAbstractUpdates.set(i, newUpdate);
                target = tb.apply(newUpdate, target);
            }

            newResult = tb.concatenated(ImmutableSLList.<Term> nil()
                    .append(newElementaryAbstractUpdates));

            if (newElementaryAbstractUpdates.equals(origAbstractUpdates)) {
                return null;
            }
        } else {
            newResult = dropEffectlessAbstractUpdateElementaries( //
                    u, target, runtimeInstance, services);
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
        } else {
            for (Term sub : concatenation.subs()) {
                result.addAll(extractAbstractUpdatesFromConcatenation(sub));
            }
        }

        return result;
    }

    private static Term dropEffectlessAbstractUpdateElementaries(Term update,
            Term target, Optional<LocationVariable> runtimeInstance, Services services) {
        final AbstractUpdate abstrUpd = (AbstractUpdate) update.op();

        final Set<AbstrUpdateUpdatableLoc> assignables = new LinkedHashSet<>();
        assignables.addAll(abstrUpd.getHasToAssignables());
        assignables.addAll(abstrUpd.getMaybeAssignables());

        final Term accessiblesTerm = update.sub(0);

        final Function allLocs = //
                services.getTypeConverter().getLocSetLDT().getAllLocs();
        final TermBuilder tb = services.getTermBuilder();

        if (abstrUpd.assignsAllLocs()) {
            /*
             * If an abstract update may change all locations, then it is never
             * effectless. However, we can simplify this to allLocs alone if
             * there are more ops in the assignable (the locset union rules
             * don't apply here since the lhs is built into the operator
             * itself).
             */
            if (assignables.size() > 1) {
                return tb.abstractUpdate(
                        services.abstractUpdateFactory().changeAssignables(
                                abstrUpd,
                                Collections.singleton(new AllLocsLoc(allLocs))),
                        accessiblesTerm);
            }

            return null;
        }

        final Pair<Set<AbstrUpdateUpdatableLoc>, Set<AbstrUpdateUpdatableLoc>> opsAnalysisResult = //
                AbstractExecutionUtils.opsAssignedBeforeUsed(target,
                        runtimeInstance, services).orElse(null);

        if (opsAnalysisResult == null) {
            return null;
        }

        final Set<AbstrUpdateUpdatableLoc> opsHaveToAssignBeforeUsed = opsAnalysisResult.first;

        /*
         * We can also remove all assignables that are not occurring at all in
         * the target. Then, we also remove them from the accessibles. TODO (DS,
         * 2019-03-01): It does not make sense to remove them from the
         * accessibles when I think about it now. Deactivated that. Maybe plug
         * it in if I'm wrong...
         */
        final Set<AbstractUpdateLoc> locsInTarget = AbstractUpdateFactory
                .extractAbstrUpdateLocsFromTerm(target, runtimeInstance,
                        services);

        // XXX Normalize "self" variables, they're different...!!!
        //FieldLoc field1Loc1 = (FieldLoc) assignables.iterator().next();
        //FieldLoc field1Loc2 = (FieldLoc) locsInTarget.iterator().next();
        //field1Loc1.equals(field1Loc2);

        final Set<AbstrUpdateLHS> newAssignables = assignables.stream()
                .filter(op -> !opsHaveToAssignBeforeUsed.contains(op))
                .filter(loc -> locsInTarget.contains(loc))
                .map(loc -> abstrUpd.hasToAssign(loc) ? new HasToLoc(loc) : loc)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

        final Set<AbstrUpdateRHS> newAccessibles = //
                AbstractUpdateFactory
                        .abstrUpdateLocsFromTerm(accessiblesTerm,
                                runtimeInstance, services)
                        .stream().map(AbstrUpdateRHS.class::cast)
                        // .filter(loc -> visitor.getResult().contains(loc))
                        .collect(Collectors
                                .toCollection(() -> new LinkedHashSet<>()));

        if (abstrUpd.getAllAssignables().stream()
                .noneMatch(op -> !newAssignables.contains(op))) {
            // No change.
            return null;
        }

        if (newAssignables.isEmpty()) {
            return tb.skip();
        }

        return tb.abstractUpdate(abstrUpd.getAbstractPlaceholderStatement(),
                newAssignables, newAccessibles);
    }

    @Override
    public String toString() {
        return String.format(
                "\\dropEffectlessAbstractUpdateElementaries(%s, %s)", uSV,
                targetSV, resultSV);
    }

}