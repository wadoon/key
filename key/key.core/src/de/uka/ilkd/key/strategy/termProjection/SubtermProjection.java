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

package de.uka.ilkd.key.strategy.termProjection;

import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.logic.calculus.PosInTerm;
import org.key_project.common.core.logic.calculus.SequentFormula;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Projection for computing a subterm of a given term. The position of the
 * subterm within the complete term is described using a <code>PosInTerm<Term></code>.
 */
public class SubtermProjection implements ProjectionToTerm {

    private final PosInTerm<Term> pit;
    private final ProjectionToTerm completeTerm;

    public static ProjectionToTerm create(ProjectionToTerm completeTerm,
                                          PosInTerm<Term> pit) {
        return new SubtermProjection ( completeTerm, pit );
    }

    private SubtermProjection(ProjectionToTerm completeTerm, PosInTerm<Term> pit) {
        this.completeTerm = completeTerm;
        this.pit = pit;
    }

    public Term toTerm(RuleApp app, PosInOccurrence<Term, SequentFormula<Term>> pos, Goal goal) {
        return pit.getSubTerm( completeTerm.toTerm ( app, pos, goal ) ) ;
    }
}