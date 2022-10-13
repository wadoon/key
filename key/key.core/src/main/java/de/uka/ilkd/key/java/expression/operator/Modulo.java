package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import java.util.List;


public final class Modulo extends BinaryOperator {
    public Modulo(PositionInfo pi, List<Comment> comments, @Nonnull Expression lhs, @Nonnull Expression rhs) {
        super(pi, comments, lhs, rhs);
    }

    public Modulo(ExtList children) {
        super(children);
    }

    public Modulo(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }


    /**
     * Get precedence.
     *
     * @return the int value.
     */
    public int getPrecedence() {
        return 2;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return INFIX;
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnModulo(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printModulo(this);
    }

}