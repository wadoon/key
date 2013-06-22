package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

import java.util.Iterator;
import java.util.Set;

/**
 * An OracleAssertion is a set of {@link OracleExpression} instances. On a FOL
 * level, it represents a set of formulas joined by disjunctions.
 * 
 * @author christopher
 * 
 */
public class OracleAssertion {

    /**
     * The expressions present in this assertion. Formally, the semantic meaning
     * of this set is Expression1 OR Expression2 ... OR ExpressionN.
     */
    private final Set<OracleExpression> expressions;

    public OracleAssertion(final Set<OracleExpression> expressions) {

        this.expressions = expressions;
    }

    /**
     * @return the expressions
     */
    public Set<OracleExpression> getExpressions() {
        return expressions;
    }

    @Override
    public String toString() {

        final StringBuilder toPrint = new StringBuilder();
        final Iterator<OracleExpression> iterator = expressions.iterator();
        while (iterator.hasNext()) {
            toPrint.append(iterator.next());

            if (iterator.hasNext()) {
                toPrint.append(" || ");
            }
        }

        return toPrint.toString();
    }
}