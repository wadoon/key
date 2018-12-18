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

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Stores the result variable of a method frame in the given schema variable
 * (via the MatchConditions). Used if you don't explicitly want to match a
 * method frame, which might, e.g., be sensible if you're interested in more
 * prefix elements (the exact type of which can not be known). Also, taclet find
 * expressions can get smaller that way.
 *
 * @author Dominic Steinhöfel
 */
public class StoreResultVarInCondition implements VariableCondition {
    private final ProgramSV resultVarSV;

    public StoreResultVarInCondition(ProgramSV resultVarSV) {
        this.resultVarSV = resultVarSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();
        final MethodFrame mf = JavaTools.getInnermostMethodFrame(
                svInst.getContextInstantiation().contextProgram(), services);

        IProgramVariable resultVar = null;
        if (mf != null) {
            resultVar = mf.getProgramVariable();
        }

        if (resultVar != null) {
            return matchCond.setInstantiations(
                    svInst.add(resultVarSV, resultVar, services));
        }

        return matchCond;
    }

    @Override
    public String toString() {
        return String.format("\\varcond (\\storeResultVarIn(%s))", resultVarSV);
    }

}
