// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.common.core.program;

import org.key_project.common.core.logic.op.SVSubstitute;

/**
 * A source element is a piece of syntax. It does not necessarily have a
 * semantics, at least none that is machinable, for instance a comment.
 */
public interface CCSourceElement<V extends ProgramVisitor, S extends CCSourceElement<V, S>>
        extends SVSubstitute {
    /**
     * Finds the source element that occurs first in the source.
     * 
     * @return the first source element in the syntactical representation of
     *         this element, may be equals to this element.
     * @see #getStartPosition()
     */
    S getFirstElement();

    /**
     * Finds the source element that occurs first in the source.
     * 
     * @return the first source element in the syntactical representation of
     *         this element, may be equals to this element.
     * @see #getStartPosition()
     */
    S getFirstElementIncludingBlocks();

    /**
     * Finds the source element that occurs last in the source.
     * 
     * @return the last source element in the syntactical representation of this
     *         element, may be equals to this element.
     * @see #getEndPosition()
     */
    S getLastElement();

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

    /**
     * calls the corresponding method of a visitor in order to perform some
     * action/transformation on this element
     * 
     * @param v
     *            the Visitor
     */
    void visit(V v);

    /**
     * This method returns true if two program parts are equal modulo renaming.
     * The equality is mainly a syntactical equality with some exceptions: if a
     * variable is declared we abstract from the name of the variable, so the
     * first declared variable gets e.g. the name decl_1, the second declared
     * decl_2 and so on. Look at the following programs: {int i; i=0;} and { int
     * j; j=0;} these would be seen like {int decl_1; decl_1=0;} and {int
     * decl_1; decl_1=0;} which are syntactical equal and therefore true is
     * returned (same thing for labels). But {int i; i=0;} and {int j; i=0;} (in
     * the second block the variable i is declared somewhere outside) would be
     * seen as {int decl_1; decl_1=0;} for the first one but {int decl_1; i=0;}
     * for the second one. These are not syntactical equal, therefore false is
     * returned.
     */
    boolean equalsModRenaming(S se,
            NameAbstractionTable<S> nat);

}
