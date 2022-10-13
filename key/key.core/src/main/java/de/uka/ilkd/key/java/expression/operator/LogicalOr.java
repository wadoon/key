package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import java.util.List;


/**
 * Logical or.
 */

public class LogicalOr extends BinaryOperator {
    public LogicalOr(PositionInfo pi, List<Comment> comments, @Nonnull Expression lhs, @Nonnull Expression rhs) {
        super(pi, comments, lhs, rhs);
    }

    public LogicalOr(ExtList children) {
        super(children);
    }


    public LogicalOr(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }


    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 11;
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
        v.performActionOnLogicalOr(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printLogicalOr(this);
    }

    public KeYJavaType getKeYJavaType(Services services, ExecutionContext ec) {
        return services.getTypeConverter().getBooleanType();
    }
}