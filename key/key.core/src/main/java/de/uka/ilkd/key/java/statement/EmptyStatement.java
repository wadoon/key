package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import java.util.List;


/**
 * Empty Java statement. In Java written as a single semicolon ";".
 */
public final class EmptyStatement extends JavaProgramElement implements Statement, TerminalProgramElement {

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes.
     */
    @Deprecated
    public EmptyStatement(ExtList children) {
        super(children);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * May contain: Comments
     */
    public EmptyStatement() {
        super();
    }

    public EmptyStatement(List<Comment> comments) {
        super(comments);
    }

    public EmptyStatement(PositionInfo pi, List<Comment> comments) {
        super(pi, comments);
    }

    public EmptyStatement(PositionInfo pos) {
        super(pos);
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnEmptyStatement(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printEmptyStatement(this);
    }

}