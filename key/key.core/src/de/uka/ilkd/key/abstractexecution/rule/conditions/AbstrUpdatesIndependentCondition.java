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

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateRHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
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
        final ExecutionContext ec = svInst.getExecutionContext();

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

        final Set<AbstrUpdateRHS> abstrUpd1Accessibles = AbstractUpdateFactory.INSTANCE
                .abstractUpdateLocsFromUnionTerm(u1Inst.sub(0), ec, services)
                .stream().map(AbstrUpdateRHS.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
        final Set<AbstrUpdateRHS> abstrUpd2Accessibles = AbstractUpdateFactory.INSTANCE
                .abstractUpdateLocsFromUnionTerm(u2Inst.sub(0), ec, services)
                .stream().map(AbstrUpdateRHS.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

        /* U1(x, ... := ...) / U2(... := x, ...) */
        if (abstrUpd1.mayAssignAny(abstrUpd2Accessibles)
                || abstrUpd2.mayAssignAny(abstrUpd1Accessibles)) {
            return null;
        }

        /* U1(allLocs := ...) / U2(... := x, ...) */
        if (abstrUpd1.assignsAllLocs() && !abstrUpd2Accessibles.isEmpty()) {
            return null;
        }

        /* U1(... := x, ...) / U2(allLocs := ...) */
        if (abstrUpd2.assignsAllLocs() && !abstrUpd1Accessibles.isEmpty()) {
            return null;
        }

        /* U1(... := allLocs) / U2(x, ... := ...) */
        if (containsAllLocs(abstrUpd1Accessibles)
                && abstrUpd2.assignsNothing()) {
            return null;
        }

        /* U1(x, ... := ...) / U2(... := allLocs) */
        if (containsAllLocs(abstrUpd2Accessibles)
                && abstrUpd1.assignsNothing()) {
            return null;
        }

        return mc;
    }

    private boolean containsAllLocs(Set<AbstrUpdateRHS> accessibles) {
        return accessibles.stream().anyMatch(AllLocsLoc.class::isInstance);
    }

    @Override
    public String toString() {
        return String.format( //
                "\\abstrUpdatesIndependent(%s, %s)", //
                u1, u2);
    }
}