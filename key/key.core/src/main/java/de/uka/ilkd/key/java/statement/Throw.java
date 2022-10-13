package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import java.util.List;

/**
 * Throw.
 */

public class Throw extends ExpressionJumpStatement {
    public Throw(PositionInfo pi, List<Comment> comments, Expression expression) {
        super(pi, comments, expression);
    }

    public Throw(Expression expr) {
        super(expr);
        if (expr == null) {
            throw new IllegalArgumentException("Throw requires one argument");
        }
    }

    /**
     * Throw.
     *
     * @param children an ExtList with all children
     */

    public Throw(ExtList children) {
        super(children);
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnThrow(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printThrow(this);
    }
}