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

/**
 * rule application with specific information how and where the rule
 * has to be applied
 */
package de.uka.ilkd.key.rule;

import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.rule.Rule;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;

public interface RuleApp {

    /**
     * returns the rule of this rule application
     */
    Rule rule();

    /**
     * returns the PositionInOccurrence (representing a SequentFormula<Term> and
     * a position in the corresponding formula) of this rule application
     */
    PosInOccurrence<Term> posInOccurrence();

    /** applies the specified rule at the specified position
     * if all schema variables have been instantiated
     * @param goal the Goal where to apply the rule
     * @return list of new created goals
     */
    ImmutableList<Goal> execute(Goal goal);

    /** returns true if all variables are instantiated
     * @return true if all variables are instantiated
     */
    boolean complete();

}