package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

import java.util.Iterator;
import java.util.Set;

/**
 * An OracleClause is a set of FOL formulas joined by disjunctions.
 * 
 * @author christopher
 * 
 */
public class OracleClause {

    private final Set<OracleExpression> expressions;

    public OracleClause(final Set<OracleExpression> expressions) {

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

        StringBuilder toPrint = new StringBuilder();
        Iterator<OracleExpression> iterator = expressions.iterator();
        while (iterator.hasNext()) {
            toPrint.append(iterator.next());

            if (iterator.hasNext()) {
                toPrint.append(" \\/ ");
            }
        }

        return toPrint.toString();
    }
}