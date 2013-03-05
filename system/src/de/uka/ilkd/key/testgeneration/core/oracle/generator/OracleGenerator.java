package de.uka.ilkd.key.testgeneration.core.oracle.generator;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.testgeneration.StringConstants;
import de.uka.ilkd.key.testgeneration.core.classabstraction.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.core.oracle.Oracle;
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

    // ****************** VISITORS ******************

    private static class OracleGenerationVisitor extends KeYTestGenTermVisitor {

        @Override
        public void visit(Term visited) {
            // TODO Auto-generated method stub
            
        }
    }
}
