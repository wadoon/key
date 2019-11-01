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

package de.uka.ilkd.key.abstractexecution.java.expression;

import java.io.IOException;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;

/**
 * An {@link AbstractExpression} "\abstract_expression e;" represents an
 * arbitrary Java expression and is handled as such. In particular, it may throw
 * an exception, and access all accessible variables / fields.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExpression extends JavaNonTerminalProgramElement
        implements Expression, AbstractProgramElement, Named {
    protected final String id;
    protected final Name name;
    protected final Comment[] comments;

    private final int hashCode;

    public AbstractExpression(String id) {
        this.id = id;
        this.name = new Name(id);
        this.comments = null;
        this.hashCode = id.hashCode();
    }

    public AbstractExpression(String id, Comment[] comments, PositionInfo pi) {
        this.id = id;
        this.name = new Name(id);
        this.comments = comments;
        this.hashCode = id.hashCode();
    }

    public AbstractExpression(ExtList children) {
        super(children);
        id = children.get(String.class);
        this.name = new Name(id);
        comments = children.get(Comment[].class);
        this.hashCode = id.hashCode();
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
    public boolean equals(Object o) {
        if (!(o instanceof AbstractExpression)) {
            return false;
        }

        return ((AbstractExpression) o).getId().equals(this.id);
    }

    @Override
    public boolean equalsModRenaming(SourceElement se, NameAbstractionTable nat) {
        return se.equals(this);
    }

    @Override
    protected int computeHashCode() {
        return hashCode;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnAbstractExpression(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter w) throws IOException {
        w.printAbstractExpression(this);
    }
    
    @Override
    public String toString() {
        return "\\abstract_expression " + id;
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        // XXX (DS, 2019-10-31): This might fail, e.g. when used as a guard...
        return javaServ.getJavaInfo().getJavaLangObject();
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return null;
    }
}