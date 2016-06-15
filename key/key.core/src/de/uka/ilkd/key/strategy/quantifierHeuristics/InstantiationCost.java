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

import org.key_project.common.core.logic.calculus.SequentFormula;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

/**
 * Feature that returns the number of branches after instantiated the quantifier
 * formula.
 */
public class InstantiationCost implements Feature {

	final private ProjectionToTerm varInst;
	
	private InstantiationCost(ProjectionToTerm var) {
		varInst = var;
	}

	public static Feature create(ProjectionToTerm varInst) {
	    return new InstantiationCost(varInst);
	}
    
	/**
	 * Compute the cost of a RuleApp.
	 */
	public RuleAppCost compute(RuleApp app, PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pos, Goal goal) {
        assert pos != null : "Projection is only applicable to rules with find";

        final JavaDLTerm formula = pos.sequentFormula ().formula ();
        final JavaDLTerm instance = varInst.toTerm ( app, pos, goal );

        return Instantiation.computeCost ( instance, formula, goal.sequent (), 
                goal.proof().getServices() );
	}
}