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
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Checks whether the first of a given pair of location set identifiers is syntactically
 * smaller than the second.
 *
 * @author Dominic Steinhoefel
 */
public class SyntacticallySmallerCondition implements VariableCondition {
    private final SchemaVariable locset1SV;
    private final SchemaVariable locset2SV;

    public SyntacticallySmallerCondition(SchemaVariable locset1SV, SchemaVariable locset2SV) {
        this.locset2SV = locset2SV;
        this.locset1SV = locset1SV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
                                 MatchConditions matchCond, Goal goal, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        final Object locset1 = svInst.getInstantiation(locset1SV);
        final Object locset2 = svInst.getInstantiation(locset2SV);

        for (Object locset : new Object[]{locset1, locset2}) {
            if (!(locset instanceof Term) || !(((Term) locset).op() instanceof Function) ||
                    ((Function) ((Term) locset).op()).sort() !=
                            services.getTypeConverter().getLocSetLDT().targetSort()) {
                return null;
            }
        }

        final Function lsFunc1 = (Function) ((Term) locset1).op();
        final Function lsFunc2 = (Function) ((Term) locset2).op();

        return lsFunc1.name().compareTo(lsFunc2.name()) < 0 ? matchCond : null;
    }

    @Override
    public String toString() {
        return String.format("\\varcond (\\syntacticallySmaller(%s, %s))", locset1SV, locset2SV);
    }

}
