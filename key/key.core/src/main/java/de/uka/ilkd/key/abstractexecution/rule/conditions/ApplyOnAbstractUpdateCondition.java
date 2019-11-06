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

import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Variable condition for applying an update on an abstract update:
 * <code>{U}U_P(assgn:=access} -->
 * U_P(assgn:={U}access}</code>
 *
 * @author Dominic Steinhoefel
 */
public final class ApplyOnAbstractUpdateCondition implements VariableCondition {
    private final UpdateSV u1SV;
    private final UpdateSV u2SV;
    private final UpdateSV resultSV;

    public ApplyOnAbstractUpdateCondition(UpdateSV uSV, UpdateSV u2SV, UpdateSV resultSV) {
        this.u1SV = uSV;
        this.u2SV = u2SV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions mc,
            Goal goal, Services services) {
        final SVInstantiations svInst = mc.getInstantiations();

        final Term u1 = (Term) svInst.getInstantiation(u1SV);
        final Term u2 = (Term) svInst.getInstantiation(u2SV);
        final Term origResult = (Term) svInst.getInstantiation(resultSV);

        if (u1 == null || u2 == null || !(u2.op() instanceof AbstractUpdate)) {
            return null;
        }

        if (origResult != null) {
            return mc;
        }

        final TermBuilder tb = services.getTermBuilder();

        final Term[] args = u2.subs().stream().map(sub -> tb.apply(u1, sub))
                .collect(Collectors.toList()).toArray(new Term[0]);
        final Term newResult = tb.abstractUpdate((AbstractUpdate) u2.op(), args);

        return mc.setInstantiations(svInst.add(resultSV, newResult, services));
    }

    @Override
    public String toString() {
        return String.format("\\applyConcreteOnAbstractUpdate(%s, %s, %s)", u1SV, u2SV, resultSV);
    }

}