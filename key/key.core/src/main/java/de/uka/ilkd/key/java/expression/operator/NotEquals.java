package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import java.util.List;

public class NotEquals extends ComparativeOperator {
    public NotEquals(PositionInfo pi, List<Comment> comments, @Nonnull Expression lhs, @Nonnull Expression rhs) {
        super(pi, comments, lhs, rhs);
    }

    /**
     * Not equals.
     *
     * @param children an ExtList with all children of this node
     *                 the first children in list will be the one on the left
     *                 side, the second the one on the  right side.
     */

    public NotEquals(ExtList children) {
        super(children);
    }


    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 6;
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnNotEquals(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printNotEquals(this);
    }
}