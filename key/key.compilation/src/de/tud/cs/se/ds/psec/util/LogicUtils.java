package de.tud.cs.se.ds.psec.util;

import de.tud.cs.se.ds.psec.compiler.exceptions.UnexpectedTranslationSituationException;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.operator.Negative;
import de.uka.ilkd.key.logic.op.LocationVariable;

/**
 * Useful methods around the logic parts of compilation.
 *
 * @author Dominic Scheurer
 */
public class LogicUtils {

    /**
     * Checks whether a given {@link Expression} is of {@link PrimitiveType}.
     * Throws an {@link UnexpectedTranslationSituationException} if the concrete
     * {@link Expression} type is not (yet) supported.
     * 
     * @param expr
     *            The {@link Expression} to check.
     * @param services
     *            The {@link Services} object which is needed, e.g., for
     *            checking {@link Literal}s.
     * @return true iff the given {@link Expression} is of
     *         {@link PrimitiveType}, and no
     *         {@link UnexpectedTranslationSituationException} has been thrown.
     */
    public static boolean isSimpleExpression(Expression expr,
            Services services) {
        if (expr instanceof LocationVariable) {
            LocationVariable locVar = (LocationVariable) expr;
            return locVar.getKeYJavaType()
                    .getJavaType() instanceof PrimitiveType;
        } else if ((expr instanceof Literal) && services != null) {
            return ((Literal) expr).getKeYJavaType(services)
                    .getJavaType() instanceof PrimitiveType;
        } else if (expr instanceof Negative) {
            return isSimpleExpression(((Negative) expr).getArguments().get(0),
                    services);
        } else {
            if (services == null) {
                throw new UnexpectedTranslationSituationException(Utilities
                        .format("Cannot decide whether expression %s is simple: Services is null",
                                expr, expr.getClass().getName()));

            } else {
                throw new UnexpectedTranslationSituationException(Utilities
                        .format("Cannot decide whether expression %s is simple: Unexpected type %s",
                                expr, expr.getClass().getName()));
            }
        }
    }

}
