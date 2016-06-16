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

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.logic.op.Junctor;
import org.key_project.common.core.logic.op.Operator;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.feature.SmallerThanFeature;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

/**
 * Ordering used to sort the clauses in a quantified formula. This ordering
 * should only be applied if at least one of the two clauses contains more than
 * one literal (otherwise, use <code>LiteralsSmallerThanFeature</code>).
 */
public class ClausesSmallerThanFeature extends SmallerThanFeature {

    private final ProjectionToTerm left, right;

    private final QuanEliminationAnalyser quanAnalyser =
        new QuanEliminationAnalyser ();
    
    // ugly
    private PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>        focus = null;
    private Services               services = null;

    private final LiteralsSmallerThanFeature litComparator;
    
    private ClausesSmallerThanFeature(ProjectionToTerm left,
                                      ProjectionToTerm right,
                                      IntegerLDT numbers) {
        this.left = left;
        this.right = right;
        this.litComparator = (LiteralsSmallerThanFeature)
                   LiteralsSmallerThanFeature.create ( left, right, numbers );
    }

    public static Feature create(ProjectionToTerm left, ProjectionToTerm right,
                                 IntegerLDT numbers) {
        return new ClausesSmallerThanFeature ( left, right, numbers );
    }

    protected boolean filter(TacletApp app, PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pos, Goal goal) {
        final JavaDLTerm leftTerm = left.toTerm ( app, pos, goal );
        final JavaDLTerm rightTerm = right.toTerm ( app, pos, goal );

        focus = pos;
        services = goal.proof ().getServices ();
        
        final ClauseCollector m1 = new ClauseCollector ();
        m1.collect ( leftTerm );
        final ClauseCollector m2 = new ClauseCollector ();
        m2.collect ( rightTerm );

        final boolean res = lessThan ( m1.getResult(), m2.getResult(), goal.proof().getServices().getCaches() );
        
        focus = null;
        services = null;
        
        return res;
    }
    
    /**
     * this overwrites the method of <code>SmallerThanFeature</code>
     */
    @Override
    protected boolean lessThan(JavaDLTerm t1, JavaDLTerm t2, ServiceCaches caches) {

        final int t1Def = quanAnalyser.eliminableDefinition ( t1, focus );
        final int t2Def = quanAnalyser.eliminableDefinition ( t2, focus );

        if ( t1Def > t2Def ) return true;
        if ( t1Def < t2Def ) return false;

        if ( t1.op () == Junctor.OR ) {
            if ( t2.op () == Junctor.OR ) {
                return super.lessThan ( t1, t2, caches );
            } else {
                return false;
            }
        } else {
            if ( t2.op () == Junctor.OR ) {
                return true;
            } else {
                return litComparator.compareTerms ( t1, t2, focus, services );
            }
        }        
    }

    private class ClauseCollector extends Collector {
        protected void collect(JavaDLTerm te) {
            final Operator op = te.op ();
            if ( op == Junctor.AND ) {
                collect ( te.sub ( 0 ) );
                collect ( te.sub ( 1 ) );
            } else {
                addTerm ( te );
            }
        }
    }

}