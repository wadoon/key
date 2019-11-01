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
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Checks whether the given formula is a locset formula, or a non-"value" LocSet
 * term.
 * 
 * @see LocSetLDT#getValue()
 * @author Dominic Steinhoefel
 */
public class IsLocsetFormulaCondition implements VariableCondition {
    private final boolean negated;
    private final SchemaVariable termSV;

    public IsLocsetFormulaCondition(SchemaVariable termSV, boolean negated) {
        this.termSV = termSV;
        this.negated = negated;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate, MatchConditions mc,
            Services services) {
        final SVInstantiations svInst = mc.getInstantiations();

        final Term term = (Term) svInst.getInstantiation(termSV);
        boolean isLocsetFormula = false;

        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        
        if (term.sort() == Sort.FORMULA) {
            // Something like "disjoint"
            isLocsetFormula = term.op() instanceof Function
                    && locSetLDT.containsFunction((Function) term.op());
        } else {
            // Any LocSet term which is not a "value" term
            isLocsetFormula = term.sort() == locSetLDT.targetSort();
            final OpCollector opColl = new OpCollector();
            term.execPostOrder(opColl);
            isLocsetFormula &= !opColl.contains(locSetLDT.getValue());
        }

        return negated ? bool2mc(!isLocsetFormula, mc) : bool2mc(isLocsetFormula, mc);
    }

    private static MatchConditions bool2mc(boolean b, MatchConditions mc) {
        return b ? mc : null;
    }

    @Override
    public String toString() {
        return String.format("\\varcond (%s\\isLocsetFormula(%s)", negated ? "\\not" : "", termSV);
    }
}