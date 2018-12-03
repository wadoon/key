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

package de.uka.ilkd.key.java.statement;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;

/**
 * An abstract placeholder statement "_abstract P;" represents an arbitrary Java
 * statement and is handled as such. In particular, it may return and throw an
 * exception, and access all accessible variables / fields. Abstract statements
 * are the core of Abstract Execution and Lazy Symbolic Execution.
 *
 * @author Dominic Steinhöfel
 */
public class AbstractPlaceholderStatement extends JavaStatement implements Named {

    // Those are used for JML to JavaDL conversions
    protected final String id;
    protected final Name name;
    protected final Comment[] comments;

    public AbstractPlaceholderStatement(String id) {
        this.id = id;
        this.name = new Name(id);
        this.comments = null;
    }

    public AbstractPlaceholderStatement(String id, Comment[] comments) {
        this.id = id;
        this.name = new Name(id);
        this.comments = comments;
    }

    public AbstractPlaceholderStatement(ExtList children) {
        super(children);
        id = children.get(String.class);
        this.name = new Name(id);
        comments = children.get(Comment[].class);
    }

    public String getId() {
        return id;
    }

    @Override
    public Name name() {
        return name;
    }

    @Override
    public Comment[] getComments() {
        return comments;
    }

    @Override
    public int hashCode() {
        return 17 * super.hashCode() + id.hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof AbstractPlaceholderStatement)) {
            return false;
        }

        return ((AbstractPlaceholderStatement) o).getId().equals(this.id);
    }

    @Override
    public boolean equalsModRenaming(SourceElement se,
            NameAbstractionTable nat) {
        return se.equals(this);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * calls the corresponding method of a visitor in order to perform some
     * action/transformation on this element
     *
     * @param v
     *            the Visitor
     */
    @Override
    public void visit(Visitor v) {
        v.performActionOnAbstractPlaceholderStatement(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printAbstractPlaceholderStatement(this);
    }
}