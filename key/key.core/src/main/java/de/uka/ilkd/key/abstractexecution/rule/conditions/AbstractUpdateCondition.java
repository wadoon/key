// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.abstractexecution.rule.conditions;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Variable condition which applies to updates that are abstract updates, i.e.,
 * their operator is a Function.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractUpdateCondition implements VariableCondition {
    private final UpdateSV u;
    private final boolean negated;

    public AbstractUpdateCondition(UpdateSV u, boolean negated) {
        this.u = u;
        this.negated = negated;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Goal goal, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();
        final Term uInst = (Term) svInst.getInstantiation(u);
        if (negated ^ uInst.op() instanceof AbstractUpdate) {
            return matchCond;
        } else {
            return null;
        }
    }

    @Override
    public String toString() {
        return String.format(//
                "%s\\abstractUpdate(%s)", negated ? "\\not" : "", u);
    }

}