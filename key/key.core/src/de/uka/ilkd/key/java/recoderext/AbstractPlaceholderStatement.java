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

import recoder.java.*;
import recoder.java.statement.JavaStatement;

/**
 * An abstract placeholder statement "_abstract P;" represents an arbitrary Java
 * statement and is handled as such. In particular, it may return and throw an
 * exception, and access all accessible variables / fields. Abstract statements
 * are the core of Abstract Execution and Lazy Symbolic Execution.
 *
 * @author Dominic Steinhöfel
 */
public class AbstractPlaceholderStatement extends JavaStatement {
    private static final long serialVersionUID = 1L;

    private StatementContainer astParent;
    private String id;

    public AbstractPlaceholderStatement(String id) {
        makeParentRoleValid();
        this.id = id;
    }

    public AbstractPlaceholderStatement() {
        this(null);
    }

    @Override
    public NonTerminalProgramElement getASTParent() {
        return astParent;
    }

    @Override
    public StatementContainer getStatementContainer() {
        return astParent;
    }

    @Override
    public void setStatementContainer(StatementContainer parent) {
        astParent = parent;
    }

    public String getId() {
        return id;
    }

    public void setId(String id) {
        this.id = id;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    @Override
    public int getChildCount() {
        return 0;
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
    @Override
    public ProgramElement getChildAt(int index) {
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        return false;
    }

    /**
     * Ensures that each child has "this" as syntactical parent.
     */
    @Override
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
    }

    @Override
    public int getChildPositionCode(ProgramElement child) {
        return -1;
    }

    public String getName() {
        return "_abstract " + id;
    }

    @Override
    public void accept(SourceVisitor visitor) {
        // TODO: Check if we have to do anything
    }

    @Override
    public Statement deepClone() {
        throw new RuntimeException("Unimplemented");
    }
}