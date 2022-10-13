package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import java.util.List;

/**
 * Binary and.
 */

public class BinaryAnd extends BinaryOperator {
    public BinaryAnd(PositionInfo pi, List<Comment> comments, @Nonnull Expression lhs, @Nonnull Expression rhs) {
        super(pi, comments, lhs, rhs);
    }

    /**
     * Binary and.
     *
     * @param children an ExtList with all children of this node
     *                 the first children in list will be the one on the left
     *                 side, the second the one on the  right side.
     */
    public BinaryAnd(ExtList children) {
        super(children);
    }


    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public final int getPrecedence() {
        return 7;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public final int getNotation() {
        return INFIX;
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnBinaryAnd(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printBinaryAnd(this);
    }


}