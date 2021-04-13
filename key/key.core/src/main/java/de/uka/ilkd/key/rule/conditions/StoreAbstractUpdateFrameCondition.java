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

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import java.util.stream.Collectors;

/**
 * Stores the frame of the given abstract update in the supplied schema variable.
 *
 * @author Dominic Steinhoefel
 */
public class StoreAbstractUpdateFrameCondition implements VariableCondition {
    private final SchemaVariable abstractUpdateSV;
    private final SchemaVariable resultVarSV;

    public StoreAbstractUpdateFrameCondition(SchemaVariable abstractUpdateSV, SchemaVariable resultVarSV) {
        this.resultVarSV = resultVarSV;
        this.abstractUpdateSV = abstractUpdateSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
                                 MatchConditions matchCond, Goal goal, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();
        final TermBuilder tb = services.getTermBuilder();

        if (svInst.getInstantiation(resultVarSV) != null) {
            return matchCond;
        }

        final Object abstractUpdate = svInst.getInstantiation(abstractUpdateSV);
        if (!(abstractUpdate instanceof Term) || !(((Term) abstractUpdate).op() instanceof AbstractUpdate)) {
            return null;
        }

        final Term frameTerm = tb.union(((AbstractUpdate) ((Term) abstractUpdate).op()).getAllAssignables().stream()
                .map(loc -> loc.toTerm(services)).collect(Collectors.toList()));

        return matchCond.setInstantiations(
                svInst.add(resultVarSV, frameTerm, services));
    }

    @Override
    public String toString() {
        return String.format("\\varcond (\\storeAbstractUpdateFrame(%s, %s))", abstractUpdateSV, resultVarSV);
    }

}
