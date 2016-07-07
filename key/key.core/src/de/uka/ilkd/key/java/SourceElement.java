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
import org.key_project.common.core.program.Position;

import de.uka.ilkd.key.java.visitor.Visitor;

/**
 * A source element is a piece of syntax. It does not necessarily have a
 * semantics, at least none that is machinable, for instance a
 * {@link recoder.java.Comment}. taken from RECODER and changed to achieve an
 * immutable structure
 */

public interface SourceElement extends CCSourceElement<Visitor, SourceElement> {

    /**
     * Pretty print.
     * 
     * @param w
     *            a pretty printer.
     * @exception IOException
     *                occasionally thrown.
     */
    void prettyPrint(PrettyPrinter w) throws java.io.IOException;

    PositionInfo getPositionInfo();

    /**
     * Finds the source element that occurs first in the source.
     * 
     * @return the first source element in the syntactical representation of
     *         this element, may be equals to this element.
     * @see #getStartPosition()
     */
    SourceElement getFirstElement();

    /**
     * Finds the source element that occurs first in the source.
     * 
     * @return the first source element in the syntactical representation of
     *         this element, may be equals to this element.
     * @see #getStartPosition()
     */
    SourceElement getFirstElementIncludingBlocks();

    /**
     * Finds the source element that occurs last in the source.
     * 
     * @return the last source element in the syntactical representation of this
     *         element, may be equals to this element.
     * @see #getEndPosition()
     */
    SourceElement getLastElement();

    /**
     * Returns the start position of the primary token of this element. To get
     * the start position of the syntactical first token, call the corresponding
     * method of <CODE>getFirstElement()</CODE>.
     * 
     * @return the start position of the primary token.
     */
    Position getStartPosition();

    /**
     * Returns the end position of the primary token of this element. To get the
     * end position of the syntactical first token, call the corresponding
     * method of <CODE>getLastElement()</CODE>.
     * 
     * @return the end position of the primary token.
     */
    Position getEndPosition();

    /**
     * Returns the relative position (number of blank heading lines and columns)
     * of the primary token of this element. To get the relative position of the
     * syntactical first token, call the corresponding method of
     * <CODE>getFirstElement()</CODE>.
     * 
     * @return the relative position of the primary token.
     */
    Position getRelativePosition();

}