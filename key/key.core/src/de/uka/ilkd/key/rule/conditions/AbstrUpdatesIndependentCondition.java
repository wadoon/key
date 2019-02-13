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
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractUpdate;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Checks whether two consecutive abstract updates (in the context of abstract
 * execution) are independent, i.e., none may write to locations that the other
 * one may read.
 *
 * @author Dominic Steinhoefel
 */
public final class AbstrUpdatesIndependentCondition
        implements VariableCondition {
    private final UpdateSV u1;
    private final UpdateSV u2;

    public AbstrUpdatesIndependentCondition(UpdateSV u1, UpdateSV u2) {
        this.u1 = u1;
        this.u2 = u2;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions mc, Services services) {
        final SVInstantiations svInst = mc.getInstantiations();
        final Operator allLocs = //
                services.getTypeConverter().getLocSetLDT().getAllLocs();
        final Term u1Inst = (Term) svInst.getInstantiation(u1);
        final Term u2Inst = (Term) svInst.getInstantiation(u2);

        if (u1Inst == null || u2Inst == null) {
            return mc;
        }

        if (!(u1Inst.op() instanceof AbstractUpdate)
                || !(u2Inst.op() instanceof AbstractUpdate)) {
            /*
             * We can assume that both updates are abstract, but they might be
             * constructed of an update junctor. In that case, we continue here.
             */
            assert u1Inst.op() instanceof UpdateJunctor
                    || u2Inst.op() instanceof UpdateJunctor;
            return null;
        }

        final AbstractUpdate abstrUpd1 = (AbstractUpdate) u1Inst.op();
        final AbstractUpdate abstrUpd2 = (AbstractUpdate) u2Inst.op();

        final Set<Operator> abstrUpd1Assignables = new LinkedHashSet<>(
                abstrUpd1.getMaybeAssignables());
        abstrUpd1Assignables.addAll(abstrUpd1.getHasToAssignables());

        final Set<Operator> abstrUpd2Assignables = new LinkedHashSet<>(
                abstrUpd2.getMaybeAssignables());
        abstrUpd2Assignables.addAll(abstrUpd2.getHasToAssignables());

        final Set<Operator> abstrUpd1Accessibles = getAccessibles(u1Inst);
        final Set<Operator> abstrUpd2Accessibles = getAccessibles(u2Inst);

        /* U1(x, ... := ...) / U2(... := x, ...) */
        if (abstrUpd1Assignables.stream()
                .anyMatch(abstrUpd2Accessibles::contains)
                || abstrUpd2Assignables.stream()
                        .anyMatch(abstrUpd1Accessibles::contains)) {
            return null;
        }

        /* U1(allLocs := ...) / U2(... := x, ...) */
        if (abstrUpd1Assignables.contains(allLocs)
                && !isEmptyLocSet(abstrUpd2Accessibles, services)) {
            return null;
        }

        /* U1(... := x, ...) / U2(allLocs := ...) */
        if (abstrUpd2Assignables.contains(allLocs)
                && !isEmptyLocSet(abstrUpd1Accessibles, services)) {
            return null;
        }

        /* U1(... := allLocs) / U2(x, ... := ...) */
        if (abstrUpd1Accessibles.contains(allLocs)
                && !isEmptyLocSet(abstrUpd2Assignables, services)) {
            return null;
        }

        /* U1(x, ... := ...) / U2(... := allLocs) */
        if (abstrUpd2Accessibles.contains(allLocs)
                && !isEmptyLocSet(abstrUpd1Assignables, services)) {
            return null;
        }

        return mc;
    }

    private static boolean isEmptyLocSet(Set<Operator> ops, Services services) {
        final Operator empty = //
                services.getTypeConverter().getLocSetLDT().getEmpty();
        return ops.isEmpty() || (ops.size() == 1 && ops.contains(empty));
    }

    private static Set<Operator> getAccessibles(final Term t) {
        final OpCollector opColl = new OpCollector();
        t.sub(0).execPostOrder(opColl);
        return opColl.ops().stream().filter(op -> op.arity() == 0)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
    }

    @Override
    public String toString() {
        return String.format( //
                "\\abstrUpdatesIndependent(%s, %s)", //
                u1, u2);
    }
}