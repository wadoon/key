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
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Checks whether the instantiation for a given schema variable is set (its
 * instantiation is not null) or not.
 *
 * @author Dominic Steinhoefel
 */
public class IsDefinedCondition implements VariableCondition {
    private final SchemaVariable svToCheck;
    private final boolean negated;

    public IsDefinedCondition(SchemaVariable svToCheck, boolean negated) {
        this.svToCheck = svToCheck;
        this.negated = negated;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.getInstantiation(svToCheck) == null) {
            return negated ? matchCond : null;
        }
        else {
            return negated ? null : matchCond;
        }
    }

    @Override
    public String toString() {
        return String.format("%s\\varcond (\\isDefined(%s))",
                negated ? "\\not " : "", svToCheck);
    }
}
