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

import org.key_project.common.core.logic.calculus.SequentFormula;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Projection for computing a subterm of a given term. The position of the
 * subterm within the complete term is described using a <code>PosInTerm<JavaDLTerm></code>.
 */
public class SubtermProjection implements ProjectionToTerm {

    private final PosInTerm<JavaDLTerm> pit;
    private final ProjectionToTerm completeTerm;

    public static ProjectionToTerm create(ProjectionToTerm completeTerm,
                                          PosInTerm<JavaDLTerm> pit) {
        return new SubtermProjection ( completeTerm, pit );
    }

    private SubtermProjection(ProjectionToTerm completeTerm, PosInTerm<JavaDLTerm> pit) {
        this.completeTerm = completeTerm;
        this.pit = pit;
    }

    public JavaDLTerm toTerm(RuleApp app, PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pos, Goal goal) {
        return pit.getSubTerm( completeTerm.toTerm ( app, pos, goal ) ) ;
    }
}