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

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

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
        final Term target = (Term) svInst.getInstantiation(targetSV);
        Term result = (Term) svInst.getInstantiation(resultSV);

        if (u == null || target == null || !(u.op() instanceof AbstractUpdate)
                || result != null) {
            return null;
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

        result = dropEffectlessAbstractUpdateElementaries( //
                u, target, result, services);

        if (result == null) {
            return null;
        }

        return mc.setInstantiations(svInst.add(resultSV, result, services));
    }

    private static Term dropEffectlessAbstractUpdateElementaries(Term update,
            Term target, Term result, Services services) {
        final AbstractUpdate abstrUpd = (AbstractUpdate) update.op();

        final Set<Operator> opsInAssignable = //
                DropEffectlessAbstractUpdateCondition
                        .collectNullaryOps(abstrUpd.lhs(), services);

        if (opsInAssignable.contains(
                services.getTypeConverter().getLocSetLDT().getAllLocs())) {
            /*
             * If an abstract update may change all locations, then it is never
             * effectless...
             */
            return null;
        }

        return null; // TODO
    }

    private static Pair<Set<Operator>, Set<Operator>> opsAssignedBeforeUsed(
            Term target, Services services) {
        final Set<Operator> assignedBeforeUsed = new LinkedHashSet<>();
        final Set<Operator> usedBeforeAssigned = new LinkedHashSet<>();

        // Skolem location set or location variable
        if (isProcVarOrSkolemLocSet(target, services)) {
            usedBeforeAssigned.add(target.op());
        }

        // Update in sequential normal form
        if (MergeRuleUtils.isUpdateNormalForm(target)) {
            //TODO
        }

        // Abstract Update

        // Any other term

        return new Pair<>(assignedBeforeUsed, usedBeforeAssigned);
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