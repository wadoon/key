package de.uka.ilkd.key.testgeneration.core.oracle.generator;

import java.util.HashSet;
import java.util.Set;

import org.hamcrest.core.IsAnything;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.testgeneration.StringConstants;
import de.uka.ilkd.key.testgeneration.core.classabstraction.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.core.oracle.Oracle;
import de.uka.ilkd.key.testgeneration.core.oracle.OracleClause;
import de.uka.ilkd.key.testgeneration.core.oracle.OracleBooleanExpression;
import de.uka.ilkd.key.testgeneration.util.parsers.AbstractTermParser;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.TermTransformerException;
import de.uka.ilkd.key.testgeneration.util.parsers.visitors.KeYTestGenTermVisitor;

/**
 * API singleton for the oraclegeneration package.
 * <p>
 * Provides services for turning the postconditions of Java methods into oracle
 * {@link Term} instances.
 * 
 * @author christopher
 */
public enum OracleGenerator {
    INSTANCE;

    private final String SEPARATOR = StringConstants.FIELD_SEPARATOR.toString();

    private final TermToOracleTransformer TERM_TO_ORACLE_TRANSFORMER = new TermToOracleTransformer(
            this.SEPARATOR);

    public Term createOracleForMethod(final KeYJavaMethod method)
            throws OracleGeneratorException {

        try {

            final Term postCondition = method.getPostconditions().get(0);
            Term oracle;

            oracle = this.TERM_TO_ORACLE_TRANSFORMER.transform(postCondition);

            return oracle;

        } catch (final TermTransformerException e) {

            throw new OracleGeneratorException(e.getMessage());
        }
    }

    public Oracle createOracle(Term postCondition)
            throws OracleGeneratorException {

        try {

            /*
             * Pre-process the postcondition, simplifying and putting it into
             * conjunctive normal form.
             */
            Term processedPostCondition = TERM_TO_ORACLE_TRANSFORMER
                    .transform(postCondition);

            return null;

        } catch (TermTransformerException e) {

            throw new OracleGeneratorException(e.getMessage());
        }
    }

    // ************************** VISITORS **************************

    private static class OracleConjunctionBuilder extends KeYTestGenTermVisitor {

        private boolean sawNot = false;

        Set<OracleClause> expressions = new HashSet<OracleClause>();

        @Override
        public void visit(Term visited) {

        }
    }

    private static class OracleDisjunctionBuilder extends KeYTestGenTermVisitor {

        private boolean sawNot;

        private boolean sawAnd;

        Set<OracleBooleanExpression> expressions = new HashSet<OracleBooleanExpression>();

        @Override
        public void visit(Term term) {

            if (sawAnd) {
                return;
            }

            if (isNot(term)) {

            }
        }
    }

    private static class OracleGeneratorParser extends AbstractTermParser {

        private void constructClause(Term term, Set<OracleClause> clauses)
                throws OracleGeneratorException {

            OracleClause clause = null;
            Set<OracleBooleanExpression> expressions = new HashSet<OracleBooleanExpression>();

            Term firstChild = term.sub(0);
            Term secondChild = term.sub(1);

            if (isAnd(firstChild)) {
                constructClause(firstChild, clauses);
                constructExpressions(secondChild, expressions);
            } else {
                constructClause(secondChild, clauses);
                constructExpressions(firstChild, expressions);
            }

            clause = new OracleClause(expressions);
            clauses.add(clause);
        }

        private void constructExpressions(Term term,
                Set<OracleBooleanExpression> expressions) throws OracleGeneratorException {

            /*
             * If the Term is an Or-term, resolve both sub-expressions
             * recursively
             */
            if (isOr(term)) {
                constructExpressions(term.sub(0), expressions);
                constructExpressions(term.sub(1), expressions);
            } else {

                OracleBooleanExpression expression = constructSingleExpression(term);
                expressions.add(expression);
            }
        }

        private OracleBooleanExpression constructSingleExpression(Term term) throws OracleGeneratorException {

            if (this.isSortedOperator(term)) {
                return this.constructExpressionFromSortedOperator(term);

            } else if (this.isIfThenElse(term)) {
                return this.constructExpressionFromIfThenElse(term);

            }

            throw new OracleGeneratorException(
                    "Attempting to construct Oracle from corrupt Term. Expected SortedOperator or IfThenElse, but found "
                            + term.op().name());
        }

        private OracleBooleanExpression constructExpressionFromIfThenElse(
                Term term) {
            // TODO Auto-generated method stub
            return null;
        }

        private OracleBooleanExpression constructExpressionFromSortedOperator(
                Term term) {
            // TODO Auto-generated method stub
            return null;
        }
    }
}