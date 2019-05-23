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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateAssgnLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.ProgVarReplacer;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Variable condition checking whether we can unify the name for an assignable
 * at the same position of two abstract updates of the same type such that the
 * result of the application on two terms is equal. For instance:
 * 
 * <code>{U_P(a, x, c := rhs)}t(x) = {U_P(a, y, c := rhs)}t(y)</code>
 * 
 * can be simplified to "true". This only works for {@link PVLoc}s.
 *
 * @author Dominic Steinhoefel
 */
public final class CanUnifyAbstrUpdLHSForTargetsCondition implements VariableCondition {
    private final UpdateSV u1SV;
    private final SchemaVariable target1SV;
    private final UpdateSV u2SV;
    private final SchemaVariable target2SV;

    public CanUnifyAbstrUpdLHSForTargetsCondition(UpdateSV u1SV, SchemaVariable target1SV,
            UpdateSV u2SV, SchemaVariable target2SV) {
        this.u1SV = u1SV;
        this.target1SV = target1SV;
        this.u2SV = u2SV;
        this.target2SV = target2SV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions mc,
            Services services) {
        final SVInstantiations svInst = mc.getInstantiations();

        final Term u1 = (Term) svInst.getInstantiation(u1SV);
        final Term target1 = (Term) svInst.getInstantiation(target1SV);
        final Term u2 = (Term) svInst.getInstantiation(u2SV);
        final Term target2 = (Term) svInst.getInstantiation(target2SV);

        if (u1 == null || target1 == null || u2 == null || target2 == null) {
            return null;
        }

        if (!(u1.op() instanceof AbstractUpdate) || !(u2.op() instanceof AbstractUpdate)) {
            return null;
        }

        final AbstractUpdate abstrUpd1 = (AbstractUpdate) u1.op();
        final AbstractUpdate abstrUpd2 = (AbstractUpdate) u2.op();

        if (!abstrUpd1.getUpdateName().equals(abstrUpd2.getUpdateName())
                || !u1.sub(0).equals(u2.sub(0))) {
            return null;
        }

        assert abstrUpd1.getAllAssignables().size() == abstrUpd2.getAllAssignables().size();

        final List<AbstractUpdateAssgnLoc> upd1assign = new ArrayList<>();
        upd1assign.addAll(abstrUpd1.getAllAssignables());
        final List<AbstractUpdateAssgnLoc> upd2assign = new ArrayList<>();
        upd2assign.addAll(abstrUpd2.getAllAssignables());

        final Map<ProgramVariable, ProgramVariable> substMap = new LinkedHashMap<>();

        for (int i = 0; i < upd1assign.size(); i++) {
            AbstractUpdateAssgnLoc upd1lhs = upd1assign.get(i);
            AbstractUpdateAssgnLoc upd2lhs = upd2assign.get(i);

            if (!upd1lhs.equals(upd2lhs)) {
                if (upd1lhs instanceof HasToLoc && upd2lhs instanceof HasToLoc) {
                    upd1lhs = ((HasToLoc) upd1lhs).child();
                    upd2lhs = ((HasToLoc) upd2lhs).child();
                }

                if (upd1lhs instanceof PVLoc && upd2lhs instanceof PVLoc) {
                    final LocationVariable subst = //
                            (LocationVariable) ((PVLoc) upd2lhs).childOps().iterator().next();
                    final LocationVariable with = //
                            (LocationVariable) ((PVLoc) upd1lhs).childOps().iterator().next();

                    substMap.put(subst, with);
                } else {
                    return null;
                }
            }
        }

        final ProgVarReplacer pvr = new ProgVarReplacer(substMap, services);
        if (target1.equals(pvr.replace(target2))) {
            return mc;
        } else {
            return null;
        }
    }

    @Override
    public String toString() {
        return String.format("\\canUnifyAbstrUpdLHSForTargets(%s, %s, %s, %s)", u1SV, target1SV,
                u2SV, target2SV);
    }

}