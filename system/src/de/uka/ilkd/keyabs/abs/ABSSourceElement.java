// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.ProgramVisitor;
import de.uka.ilkd.key.util.ExtList;

/**
 * Top level implementation of a Java {@link SourceElement}. taken from COMPOST
 * and changed to achieve an immutable structure
 */
public abstract class ABSSourceElement implements SourceElement {

    private final PositionInfo posInfo;

    /**
     * Java source element.
     */
    public ABSSourceElement() {
        posInfo = PositionInfo.UNDEFINED;
    }

    /**
     * Java source element.
     * 
     * @param pi
     *            PositionInfo the PositionInfo of the element
     */
    public ABSSourceElement(PositionInfo pi) {
        posInfo = getPosInfo(pi);
    }

    /**
     * Java source element.
     * 
     * @param children
     *            a list of the children of this element. May contain:
     *            PositionInfo
     */
    public ABSSourceElement(ExtList children) {
        posInfo = getPosInfo(children.get(PositionInfo.class));

    }

    public ABSSourceElement(ExtList children, PositionInfo pos) {
        posInfo = getPosInfo(pos);
    }

    /**
     * internal method use to guarantee the position info object is always not
     * the null reference
     * 
     * @param p
     *            a PositionInfo
     * @return if <tt>p</tt> is <tt>null</tt> the undefined position (
     *         {@link PositionInfo#UNDEFINED}) is returned otherwise <tt>p</tt>
     */
    private static PositionInfo getPosInfo(PositionInfo p) {
        final PositionInfo pos;
        if (p == null) {
            pos = PositionInfo.UNDEFINED;
        } else {
            pos = p;
        }
        return pos;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some
     * action/transformation on this element
     * 
     * @param v
     *            the Visitor
     */
    @Override
    public void visit(ProgramVisitor v) {
        visit((ABSVisitor) v);
    }

    public abstract void visit(ABSVisitor v);

    /**
     * Finds the source element that occurs first in the source. The default
     * implementation returns this element, which is correct for all terminal
     * program elements, and many non terminals such as statements and prefixed
     * operators.
     * 
     * @return the first source element in the syntactical representation of
     *         this element, may be equals to this element.
     * @see #toSource()
     * @see #getStartPosition()
     */

    @Override
    public SourceElement getFirstElement() {
        return this;
    }

    /**
     * Finds the source element that occurs last in the source. The default
     * implementation returns this element, which is correct for all terminal
     * program elements, and many non terminals such as statements and prefixed
     * operators.
     * 
     * @return the last source element in the syntactical representation of this
     *         element, may be equals to this element.
     * @see #toSource()
     * @see #getEndPosition()
     */

    @Override
    public SourceElement getLastElement() {
        return this;
    }

    /**
     * Creates a syntactical representation of the source element using the
     * {@link #prettyPrint} method.
     */

    public String toSource() {
        return toString();
    }

    /**
     * Returns the start position of the primary token of this element. To get
     * the start position of the syntactical first token, call the corresponding
     * method of <CODE>getFirstElement()</CODE>.
     * 
     * @return the start position of the primary token.
     */
    @Override
    public Position getStartPosition() {
        return posInfo.getStartPosition();
    }

    /**
     * Returns the end position of the primary token of this element. To get the
     * end position of the syntactical first token, call the corresponding
     * method of <CODE>getLastElement()</CODE>.
     * 
     * @return the end position of the primary token.
     */
    @Override
    public Position getEndPosition() {
        return posInfo.getEndPosition();
    }

    /**
     * Returns the relative position (number of blank heading lines and columns)
     * of the primary token of this element. To get the relative position of the
     * syntactical first token, call the corresponding method of
     * <CODE>getFirstElement()</CODE>.
     * 
     * @return the relative position of the primary token.
     */
    @Override
    public Position getRelativePosition() {
        return posInfo.getRelativePosition();
    }

    @Override
    public PositionInfo getPositionInfo() {
        return posInfo;
    }

    /**
     * this violates immutability, but the method is only called right after the
     * object is created...
     */
    protected void setParentClass(String s) {
        posInfo.setParentClass(s);
    }

    /** get the class the statement originates from */
    public String getParentClass() {
        return posInfo.getParentClass();
    }

}
