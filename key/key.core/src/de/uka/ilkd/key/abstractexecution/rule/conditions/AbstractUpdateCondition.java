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
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Variable condition which applies to updates that are abstract updates, i.e.,
 * their operator is a Function.
 *
 * @author Dominic Steinhöfel
 */
public class AbstractUpdateCondition implements VariableCondition {
    private final UpdateSV u;
    private final boolean negated;

    public AbstractUpdateCondition(UpdateSV u, boolean negated) {
        this.u = u;
        this.negated = negated;
    }

    /**
     * @param updateTerm
     *            The term to check.
     * @return true iff target is an update with a function symbol as operator,
     *         i.e., an abstract update.
     */
    public static boolean isAbstractUpdate(Term updateTerm) {
        final OpCollector opColl = new OpCollector();
        updateTerm.execPostOrder(opColl);
        return opColl.ops().stream().anyMatch(op -> op instanceof AbstractUpdate);
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();
        final Term uInst = (Term) svInst.getInstantiation(u);
        if (negated ^ isAbstractUpdate(uInst)) {
            return matchCond;
        }
        else {
            return null;
        }
    }

    @Override
    public String toString() {
        return String.format( //
                "%s\\abstractUpdate(%s)", negated ? "\\not" : "", u);
    }

}
