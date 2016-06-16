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

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.JavaDLVisitor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;


/**
 * Feature for checking if the term of the first projection contains the
 * term of the second projection.
 */
public class ContainsTermFeature implements Feature {

    /** Constant that represents the boolean value true */
    public static final RuleAppCost ZERO_COST = NumberRuleAppCost.getZeroCost();

    /** Constant that represents the boolean value false */
    public static final RuleAppCost TOP_COST = TopRuleAppCost.INSTANCE;

    private final ProjectionToTerm proj1;

    private final ProjectionToTerm proj2;


    /**
     * @param proj        the ProjectionToTerm to the instantiation is supposed
     *                    to be inspected
     * @param termFeature the term feature to use
     * @param noInstCost  result if <code>schemaVar</code> is not instantiated
     * @param demandInst  if <code>true</code> then raise an exception if
     *                    <code>schemaVar</code> is not instantiated (otherwise:
     *                    return <code>noInstCost</code>)
     */
    private ContainsTermFeature(ProjectionToTerm proj1,
                                ProjectionToTerm proj2) {
        this.proj1 = proj1;
        this.proj2 = proj2;
    }


    public static Feature create(ProjectionToTerm proj1,
                                 ProjectionToTerm proj2) {
        return new ContainsTermFeature(proj1, proj2);
    }


    @Override
    public RuleAppCost compute(RuleApp app,
                               PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pos,
                               Goal goal) {
        final JavaDLTerm t1 = proj1.toTerm(app, pos, goal);
        final JavaDLTerm t2 = proj2.toTerm(app, pos, goal);
        ContainsTermVisitor visitor = new ContainsTermVisitor(t2);
        t1.execPreOrder(visitor);
        if (visitor.found) {
            return ZERO_COST;
        } else {
            return TOP_COST;
        }
    }


    private class ContainsTermVisitor implements JavaDLVisitor {
        boolean found = false;
        JavaDLTerm term;


        public ContainsTermVisitor(JavaDLTerm term) {
            this.term = term;
        }

        @Override
        public boolean visitSubtree(JavaDLTerm visited) {
            return true;
        }

        @Override
        public void visit(JavaDLTerm visited) {
            found = found || visited.equalsModRenaming(term);
        }

        @Override
        public void subtreeEntered(JavaDLTerm subtreeRoot) {
            // nothing to do
        }

        @Override
        public void subtreeLeft(JavaDLTerm subtreeRoot) {
            // nothing to do
        }
    }
}