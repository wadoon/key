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

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.AbstractExecutionUtils;

/**
 * Checks whether an abstract update assigns to a given variable.
 *
 * @author Dominic Steinhöfel
 */
public class AssignsCondition implements VariableCondition {
    private final UpdateSV updateSV;
    private final ProgramSV progvarSV;
    private final boolean negated;

    public AssignsCondition(UpdateSV updateSV, ProgramSV progvarSV,
            boolean negated) {
        this.updateSV = updateSV;
        this.progvarSV = progvarSV;
        this.negated = negated;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        final Term update = (Term) svInst.getInstantiation(updateSV);
        final LocationVariable progvar = (LocationVariable) svInst
                .getInstantiation(progvarSV);

        return negated
                ^ AbstractExecutionUtils.getAssignablesForAbstractUpdate(update)
                        .stream().anyMatch(op -> op.equals(progvar)) ? matchCond
                                : null;
    }

    @Override
    public String toString() {
        return String.format("%s\\varcond (\\assigns(%s, %s))",
                negated ? "\\not " : "", updateSV, progvarSV);
    }
}
