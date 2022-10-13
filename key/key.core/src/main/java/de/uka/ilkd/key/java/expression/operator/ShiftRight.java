package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import java.util.List;


public class ShiftRight extends BinaryOperator {
    public ShiftRight(PositionInfo pi, List<Comment> comments, @Nonnull Expression lhs, @Nonnull Expression rhs) {
        super(pi, comments, lhs, rhs);
    }

    /**
     * Shift right.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */
    public ShiftRight(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * The first occurrence of an Expression in the given list is taken as
     * the left hand side
     * of the expression, the second occurrence is taken as the right hand
     * side of the expression.
     *
     * @param children the children of this AST element as KeY classes.
     */
    public ShiftRight(ExtList children) {
        super(children);
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 4;
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
        v.performActionOnShiftRight(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printShiftRight(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        final TypeConverter tc = javaServ.getTypeConverter();
        return tc.getPromotedType
                (tc.getKeYJavaType((Expression) getChildAt(0), ec));
    }
}