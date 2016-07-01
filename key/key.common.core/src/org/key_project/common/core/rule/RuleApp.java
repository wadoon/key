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
package org.key_project.common.core.rule;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.proof.CCGoal;
import org.key_project.util.collection.ImmutableList;

public interface RuleApp<T extends CCTerm<?, ?, ?, T>, G extends CCGoal<?, T, ?, ?, ?>> {

    /**
     * returns the rule of this rule application
     */
    Rule rule();

    /**
     * returns the PositionInOccurrence (representing a SequentFormula<Term> and
     * a position in the corresponding formula) of this rule application
     */
    PosInOccurrence<T> posInOccurrence();

    /** applies the specified rule at the specified position
     * if all schema variables have been instantiated
     * @param goal the Goal where to apply the rule
     * @return list of new created goals
     */
    ImmutableList<G> execute(G goal);

    /** returns true if all variables are instantiated
     * @return true if all variables are instantiated
     */
    boolean complete();

}