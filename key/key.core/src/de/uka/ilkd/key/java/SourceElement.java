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

package de.uka.ilkd.key.java;

import java.io.IOException;

import org.key_project.common.core.program.CCSourceElement;

import de.uka.ilkd.key.java.visitor.Visitor;

/**
 *  A source element is a piece of syntax. It does not necessarily have
 *  a semantics, at least none that is machinable, for instance a
 *  {@link recoder.java.Comment}.
 * taken from RECODER and changed to achieve an immutable structure
 */

public interface SourceElement extends CCSourceElement<Visitor, SourceElement> {

    /**
     * Pretty print.
     * @param w a pretty printer.
     * @exception IOException occasionally thrown.
     */
    void prettyPrint(PrettyPrinter w) throws java.io.IOException;

    PositionInfo getPositionInfo();

}