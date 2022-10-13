package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import java.util.List;

/**
 * Comparative operator.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class ComparativeOperator extends BinaryOperator {
    public ComparativeOperator(PositionInfo pi, List<Comment> comments, @Nonnull Expression lhs, @Nonnull Expression rhs) {
        super(pi, comments, lhs, rhs);
    }

    /**
     * Comparative operator.
     *
     * @param children an ExtList with all children of this node
     *                 the first children in list will be the one on the left
     *                 side, the second the one on the  right side.
     */

    public ComparativeOperator(ExtList children) {
        super(children);
    }

    public ComparativeOperator(Expression lhs, Expression rhs) {
        this(null, null, lhs, rhs);
    }


    /**
     * Get notation.
     *
     * @return the int value.
     */
    public int getNotation() {
        return INFIX;
    }

    public KeYJavaType getKeYJavaType(Services services, ExecutionContext ec) {
        return getKeYJavaType(services);
    }

    public KeYJavaType getKeYJavaType(Services services) {
        return services.getTypeConverter().getBooleanType();
    }

}