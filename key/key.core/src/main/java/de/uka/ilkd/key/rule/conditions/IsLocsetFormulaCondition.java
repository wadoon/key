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
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Checks whether the given formula is a locset formula.
 *
 * @author Dominic Steinhoefel
 */
public class IsLocsetFormulaCondition implements VariableCondition {
    private final boolean negated;
    private final SchemaVariable formulaSV;

    public IsLocsetFormulaCondition(SchemaVariable formulaSV, boolean negated) {
        this.formulaSV = formulaSV;
        this.negated = negated;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate, MatchConditions mc,
            Services services) {
        final SVInstantiations svInst = mc.getInstantiations();

        final Term formula = (Term) svInst.getInstantiation(formulaSV);
        final boolean isLocsetFormula = formula.op() instanceof Function && services
                .getTypeConverter().getLocSetLDT().containsFunction((Function) formula.op());

        return negated ? bool2mc(!isLocsetFormula, mc) : bool2mc(isLocsetFormula, mc);
    }

    private static MatchConditions bool2mc(boolean b, MatchConditions mc) {
        return b ? mc : null;
    }

    @Override
    public String toString() {
        return String.format("\\varcond (%s\\isLabeled(%s)", negated ? "\\not" : "", formulaSV);
    }
}