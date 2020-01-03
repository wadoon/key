// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.abstractexecution.java;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractStatement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.Named;

/**
 * {@link AbstractProgramElement}s are the core of <em>Abstract Execution</em>.
 * So far, {@link AbstractStatement}s and {@link AbstractExpression}s are
 * implemented.
 *
 * @author Dominic Steinhoefel
 */
public interface AbstractProgramElement extends ProgramElement, Named {
    /**
     * @return The identifier of this {@link AbstractProgramElement}.
     */
    String getId();
}
