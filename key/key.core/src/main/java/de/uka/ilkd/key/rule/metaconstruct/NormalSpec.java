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

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

/**
 * Term transformer which relates, in the context of Abstract Execution, the
 * "normal" termination flag of an {@link AbstractPlaceholderStatement} with a
 * potentially existing normal_behavior precondition. More precisely, it creates
 * the formula "(normal <-> PRECONDITION) & (normal -> POSTCONDITION)".
 *
 * @author Dominic Steinhoefel
 */
public class NormalSpec extends RetrieveAESpecTransformer {
    public NormalSpec() {
        super("#normalSpec", Behavior.NORMAL_BEHAVIOR, true);
    }
}