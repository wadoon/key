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
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateAssgnLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
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
 * Variable condition for dropping abstract updates only writing to locations
 * that are not occurring in the target or are overwritten before being read.
 *
 * @author Dominic Steinhoefel
 */
public final class DropEffectlessAbstractUpdateCondition implements VariableCondition {
    private final UpdateSV uSV;
    private final SchemaVariable targetSV;
    private final SchemaVariable resultSV;

    public DropEffectlessAbstractUpdateCondition(UpdateSV uSV, SchemaVariable targetSV,
            SchemaVariable resultSV) {
        this.uSV = uSV;
        this.targetSV = targetSV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions mc,
            Services services) {
        final SVInstantiations svInst = mc.getInstantiations();

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
             * TODO (DS, 2019-01-04): CHECK MATCHING FOR NONRIGID TERMS! Actually, the
             * taclets using this condition only match on nonrigid targets. For some reason,
             * however, this matching does not work (i.e., the taclets are also applied to
             * rigid targets). That shouldn't do any harm, but we have other taclets for
             * these cases. We should in any case check why the matching does not work...
             */
            return null;
        }

        if (target.containsJavaBlockRecursive()) {
            return null;
        }

        if (u.op() == UpdateJunctor.CONCATENATED_UPDATE) {
            final List<Term> origAbstractUpdates = //
                    Collections.unmodifiableList(extractAbstractUpdatesFromConcatenation(u));
            final LinkedList<Term> newElementaryAbstractUpdates = new LinkedList<>();

            final TermBuilder tb = services.getTermBuilder();
            for (int i = origAbstractUpdates.size() - 1; i >= 0; i--) {
                final Term elementaryAbstrUpd = //
                        origAbstractUpdates.get(i);
                if (!mayDropAbstractUpdate(elementaryAbstrUpd, target, runtimeInstance, services)) {
                    newElementaryAbstractUpdates.addFirst(elementaryAbstrUpd);
                    target = tb.apply(elementaryAbstrUpd, target);
                }
            }

            newResult = tb
                    .concatenated(ImmutableSLList.<Term>nil().append(newElementaryAbstractUpdates));

            if (newElementaryAbstractUpdates.equals(origAbstractUpdates)) {
                return null;
            }
        } else if (u.op() instanceof AbstractUpdate) {
            if (mayDropAbstractUpdate(u, target, runtimeInstance, services)) {
                newResult = services.getTermBuilder().skip();
            } else {
                return null;
            }
        } else {
            return null;
        }

        if (newResult == null) {
            return null;
        }

        return mc.setInstantiations(svInst.add(resultSV, newResult, services));
    }

    private static List<Term> extractAbstractUpdatesFromConcatenation(Term concatenation) {
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

    private static boolean mayDropAbstractUpdate(Term update, Term target,
            Optional<LocationVariable> runtimeInstance, Services services) {
        final AbstractUpdate abstrUpd = (AbstractUpdate) update.op();

        final Set<AbstractUpdateAssgnLoc> assignables = new LinkedHashSet<>();
        assignables.addAll(abstrUpd.getHasToAssignables());
        assignables.addAll(abstrUpd.getMaybeAssignables());

        if (abstrUpd.assignsAllLocs()) {
            /*
             * If an abstract update may change all locations, then it is never effectless.
             */
            return false;
        }

        final Pair<Set<AbstractUpdateAssgnLoc>, Set<AbstractUpdateLoc>> opsAnalysisResult = //
                AbstractExecutionUtils.opsAssignedBeforeUsed(target, runtimeInstance, services)
                        .orElse(null);

        if (opsAnalysisResult == null) {
            return false;
        }

        final Set<AbstractUpdateAssgnLoc> opsHaveToAssignBeforeUsed = opsAnalysisResult.first;

        /*
         * We can also remove all assignables that are not occurring at all in the
         * target. Then, we also remove them from the accessibles. TODO (DS,
         * 2019-03-01): It does not make sense to remove them from the accessibles when
         * I think about it now. Deactivated that. Maybe plug it in if I'm wrong...
         */
        final Set<AbstractUpdateLoc> locsInTarget = AbstractUpdateFactory
                .extractAbstrUpdateLocsFromTerm(target, runtimeInstance, services);

        final long effectiveAssignables = assignables.stream()
                .filter(assignable -> !opsHaveToAssignBeforeUsed.contains(assignable))
                .filter(assignable -> locsInTarget.stream()
                        .anyMatch(targetLoc -> assignable.mayAssign(targetLoc)))
                .count();

        return effectiveAssignables == 0;
    }

    @Override
    public String toString() {
        return String.format("\\dropEffectlessAbstractUpdate(%s, %s)", uSV, targetSV, resultSV);
    }

}