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

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Interface for mappings from rule applications to terms. This is used, for
 * instance, for determining the instantiation of a schema variable. We also
 * allow projections to be partial, which is signalled by <code>toTerm</code>
 * returning <code>null</code>
 */
public interface ProjectionToTerm {
    Term toTerm (RuleApp<Term, Goal> app, PosInOccurrence<Term> pos, Goal goal );
}