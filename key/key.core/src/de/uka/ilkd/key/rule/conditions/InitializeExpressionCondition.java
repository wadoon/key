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
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Instantiates a {@link ProgramSV} with a fresh variable of the given type.
 *
 * @author Dominic Steinhöfel
 */
public class InitializeExpressionCondition implements VariableCondition {
    private final ProgramSV expressionSV;
    private final KeYJavaType type;
    private final SchemaVariable initSV;

    public InitializeExpressionCondition(ProgramSV expressionSV,
            KeYJavaType type, SchemaVariable initSV) {
        this.expressionSV = expressionSV;
        this.type = type;
        this.initSV = initSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.isInstantiated(expressionSV)) {
            return matchCond;
        }

        final IntegerLDT integerLDT = //
                services.getTypeConverter().getIntegerLDT();

        if (!type.getSort().equals(integerLDT.targetSort())) {
            /*
             * NOTE (DS, 2019-02-22): We so far only support integers. Can be
             * extended in the future if needed.
             */
            return null;
        }

        final Term instantiation = (Term) svInst.getInstantiation(initSV);
        if (instantiation == null) {
            return matchCond;
        }

        return matchCond.setInstantiations(
                svInst.add(expressionSV, instantiation, services));
    }

    @Override
    public String toString() {
        return String.format("\\varcond(\\initializeExpression(%s, %s, %s))",
                expressionSV, type, initSV);
    }
}
