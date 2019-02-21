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
import de.uka.ilkd.key.logic.FilterVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Checks whether a given term contains a predicate labeled with "<<AEPred>>".
 *
 * @author Dominic Steinhöfel
 */
public class HasAEPredicateCondition implements VariableCondition {
    private final SchemaVariable phiSV;

    public HasAEPredicateCondition(SchemaVariable phiSV) {
        this.phiSV = phiSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();
        final Term phi = (Term) svInst.getInstantiation(phiSV);

        final TermLabel aeLabel = ParameterlessTermLabel.AE_EQUIV_PROOF_LABEL;
        final Sort booleanSort = //
                services.getTypeConverter().getBooleanLDT().targetSort();
        final FilterVisitor visitor = new FilterVisitor( //
                t -> t.containsLabel(aeLabel) && //
                        !t.subs().isEmpty() && //
                        t.sub(t.subs().size() - 1).sort() == booleanSort);
        phi.execPostOrder(visitor);

        return visitor.result().isEmpty() ? null : matchCond;
    }

    @Override
    public String toString() {
        return String.format("\\varcond (\\hasAEPredicate(%s))", phiSV);
    }
}
