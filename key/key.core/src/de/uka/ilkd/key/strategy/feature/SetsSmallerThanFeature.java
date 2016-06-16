// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.feature;

import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;


public class SetsSmallerThanFeature extends SmallerThanFeature {

    private final ProjectionToTerm left, right;
    private final LocSetLDT locSetLDT;


    private SetsSmallerThanFeature(ProjectionToTerm left,
                                   ProjectionToTerm right,
                                   LocSetLDT locSetLDT) {
        this.left = left;
        this.right = right;
        this.locSetLDT = locSetLDT;
    }


    public static Feature create(ProjectionToTerm left,
                                 ProjectionToTerm right,
                                   LocSetLDT locSetLDT) {
        return new SetsSmallerThanFeature(left, right, locSetLDT);
    }


    @Override
    protected boolean filter(TacletApp app,
                             PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pos,
                             Goal goal) {
        final JavaDLTerm leftTerm = left.toTerm(app, pos, goal);
        final JavaDLTerm rightTerm = right.toTerm(app, pos, goal);

        return origLessThan(leftTerm, rightTerm, goal.proof().getServices().getCaches());
    }


    protected boolean origLessThan(JavaDLTerm leftTerm,
                                   JavaDLTerm rightTerm, ServiceCaches caches) {// TODO: Why is this method needed?
        final LiteralCollector m1 = new LiteralCollector();
        m1.collect(leftTerm);
        final ImmutableList<JavaDLTerm> literalsLeftTerm = m1.getResult();

        final LiteralCollector m2 = new LiteralCollector();
        m2.collect(rightTerm);
        final ImmutableList<JavaDLTerm> literalsRightTerm = m2.getResult();

        return super.lessThan(literalsLeftTerm, literalsRightTerm, caches);
    }


    private class LiteralCollector extends Collector {

        protected void collect(JavaDLTerm te) {
            final Operator op = te.op();
            if (op == locSetLDT.getUnion() ||
                    op == locSetLDT.getIntersect() ||
                      op == locSetLDT.getDisjoint()) {
                collect(te.sub(0));
                collect(te.sub(1));
            } else {
                addTerm(te);
            }
        }
    }

}