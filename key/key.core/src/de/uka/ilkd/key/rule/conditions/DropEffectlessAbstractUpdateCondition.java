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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgVarAndLocSetsCollector;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractUpdate;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public final class DropEffectlessAbstractUpdateCondition
        implements VariableCondition {
    private final UpdateSV u;
    private final SchemaVariable x;

    public DropEffectlessAbstractUpdateCondition(UpdateSV u, SchemaVariable x) {
        this.u = u;
        this.x = x;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions mc, Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        Term uInst = (Term) svInst.getInstantiation(u);
        Term xInst = (Term) svInst.getInstantiation(x);

        if (uInst == null || xInst == null
                || !(uInst.op() instanceof AbstractUpdate)) {
            return null;
        }

        if (xInst.isRigid()) {
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

        return dropEffectlessAbstractUpdate(uInst, xInst, services) ? mc : null;
    }

    private static boolean dropEffectlessAbstractUpdate(Term update,
            Term target, Services services) {
        final AbstractUpdate abstrUpd = (AbstractUpdate) update.op();

        final Set<Operator> opsInTarget = collectNullaryOps(target, services);
        final Set<Operator> opsInAssignable = //
                collectNullaryOps(abstrUpd.lhs(), services);

        if (opsInAssignable.contains(
                services.getTypeConverter().getLocSetLDT().getAllLocs())) {
            /*
             * If an abstract update may change all locations, then it is never
             * effectless...
             */
            return false;
        }

        if (opsInTarget.contains(
                services.getTypeConverter().getLocSetLDT().getAllLocs())) {
            /*
             * Here, there are several possibilities. One of those is that the
             * allLocs locset occurs in the accessible part of an abstract
             * update or an abstract placeholder statement. In these cases, we
             * may not drop the update.
             *
             * TODO (DS, 2019-01-04): We might want to rule out the case that
             * the allLocs occurs in the *assignable* part of a subsequent
             * abstract update (and nowhere else, or only in other such safe
             * places), in that case, we can drop the update.
             */
            return false;
        }

        return opsInTarget.stream()
                .noneMatch(op -> opsInAssignable.contains(op));
    }

    @Override
    public String toString() {
        return String.format("\\dropEffectlessAbstractUpdate(%s, %s)", u, x);
    }

    public static Set<Operator> collectNullaryOps(Term t, Services services) {
        TermNullaryOpCollector collector = new TermNullaryOpCollector(services);
        t.execPostOrder(collector);
        return collector.result();
    }

    private static class TermNullaryOpCollector extends DefaultVisitor {
        private final Set<Operator> result = new LinkedHashSet<>();
        private final Services services;

        public TermNullaryOpCollector(Services services) {
            this.services = services;
        }

        @Override
        public void visit(Term t) {
            if (t.op().arity() == 0) {
                result.add(t.op());
            }

            if (!t.javaBlock().isEmpty()) {
                final ProgVarAndLocSetsCollector pvc = //
                        new ProgVarAndLocSetsCollector( //
                                t.javaBlock().program(), services);
                pvc.start();
                result.addAll(pvc.result());
            }
        }

        public Set<Operator> result() {
            return result;
        }
    }
}