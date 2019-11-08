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

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractStatement;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

/**
 * Term transformer which relates, in the context of Abstract Execution, the
 * abstract continues term of an {@link AbstractStatement} with a potentially
 * existing continues behavior precondition.
 *
 * @author Dominic Steinhoefel
 */
public class ContinuesPrecondition extends RetrieveAEPreconditionTransformer {
    public ContinuesPrecondition() {
        super("#continuesPrecondition", Behavior.CONTINUE_BEHAVIOR);
    }
}