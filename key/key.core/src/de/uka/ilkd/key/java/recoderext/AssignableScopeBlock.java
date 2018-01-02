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

package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.ExpressionContainer;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.StatementContainer;
import recoder.java.statement.JavaStatement;

/**
 * TODO
 *
 * @author Mattias Ulbrich
 */
public class AssignableScopeBlock extends JavaStatement
        implements StatementContainer, ExpressionContainer {
    private static final long serialVersionUID = -7936276773427061881L;

    protected Expression assignable;
    protected Statement body;

    /**
     * This constructor should only be used in the SchemaJavaParser! Make sure
     * to call {@link #setBody(Statement)} and
     * {@link #setIndexPV(Expression)} afterward.
     */
    public AssignableScopeBlock() {
        this.assignable = null;
        this.body = null;
    }

    public AssignableScopeBlock(Expression assignable, StatementBlock body) {
        this.assignable = assignable;
        this.body = body;
        makeParentRoleValid();
    }

    protected AssignableScopeBlock(AssignableScopeBlock proto) {
        super(proto);
        if (proto.assignable != null) {
            this.assignable = proto.assignable.deepClone();
        }
        if (proto.body != null) {
            body = proto.body.deepClone();
        }
        makeParentRoleValid();
    }


    /**
     * Gets the assignable.
     *
     * @return the assignable
     */
    public Expression getAssignable() {
        return assignable;
    }

    /**
     * Sets the assignable.
     *
     * @param assignable the new assignable
     */
    public void setAssignable(Expression assignable) {
        this.assignable = assignable;
    }

    /**
     * Set body.
     *
     * @param body
     *            the Statement
     */
    public void setBody(Statement body) {
        this.body = body;
    }

    /**
     * Get body.
     *
     * @return the Statement
     */
    public Statement getBody() {
        return body;
    }

    /**
     * Finds the source element that occurs first in the source. Returns the
     * first element of the first child.
     *
     * @return the last source element in the syntactical representation of this
     *         element, may be equals to this element.
     */

    public SourceElement getFirstElement() {
        return getChildAt(0).getFirstElement();
    }

    /**
     * Finds the source element that occurs last in the source. Returns the last
     * element of the body.
     *
     * @return the last source element in the syntactical representation of this
     *         element, may be equals to this element.
     */

    public SourceElement getLastElement() {
        return body.getLastElement();
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (assignable != null)
            result++;
        if (body != null)
            result++;
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child
     * array
     *
     * @param index
     *            an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException
     *                if <tt>index</tt> is out of bounds
     */

    public ProgramElement getChildAt(int index) {
        if (assignable != null) {
            if (index == 0)
                return assignable;
            index--;
        }
        if (body != null) {
            if (index == 0)
                return body;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role -/0: assignable
        // role 2/1: body
        if (assignable == child) {
            return 0;
        }

        if (body == child) {
            return (assignable != null) ? 2 : 1;
        }
        return -1;
    }

    /**
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */
    public int getStatementCount() {
        int result = (body != null) ? 1 : 0;
        return result;
    }

    /**
     * Return the statement at the specified index in this node's "virtual"
     * statement array.
     *
     * @param index
     *            an index for a statement.
     * @return the statement with the given index.
     * @exception ArrayIndexOutOfBoundsException
     *                if <tt>index</tt> is out of bounds.
     */
    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */
    public int getExpressionCount() {
        return (assignable != null) ? 1 : 0;
    }

    /**
     * Return the expression at the specified index in this node's "virtual"
     * expression array.
     *
     * @param index
     *            an index for a expression.
     * @return the expression with the given index.
     * @exception ArrayIndexOutOfBoundsException
     *                if <tt>index</tt> is out of bounds.
     */

    public Expression getExpressionAt(int index) {
        if (assignable != null && index == 0) {
            return assignable;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Replace a single child in the current node. The child to replace is
     * matched by identity and hence must be known exactly. The replacement
     * element can be null - in that case, the child is effectively removed. The
     * parent role of the new child is validated, while the parent link of the
     * replaced child is left untouched.
     *
     * @param p
     *            the old child.
     * @param q
     *            the new child.
     * @return true if a replacement has occured, false otherwise.
     * @exception ClassCastException
     *                if the new child cannot take over the role of the old one.
     */
    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (assignable == p) {
            Expression r = (Expression) q;
            assignable = r;
            if (r != null) {
                r.setExpressionContainer(this);
            }
            return true;
        } else if (body == p) {
            Statement r = (Statement) q;
            body = r;
            if (r != null) {
                r.setStatementContainer(this);
            }
            return true;
        }
        return false;
    }

    /**
     * Ensures that each child has "this" as syntactical parent.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (assignable != null) {
            assignable.setExpressionContainer(this);
        }
        if (body != null) {
            body.setStatementContainer(this);
        }
    }

    // don't think we need it
    public void accept(SourceVisitor v) {
    }

    /**
     * Deep clone.
     *
     * @return the object
     */
    public AssignableScopeBlock deepClone() {
        return new AssignableScopeBlock(this);
    }

}