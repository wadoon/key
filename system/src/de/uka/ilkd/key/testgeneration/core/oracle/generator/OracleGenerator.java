package de.uka.ilkd.key.testgeneration.core.oracle.generator;

import java.util.HashSet;
import java.util.Set;

import org.hamcrest.core.IsAnything;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.testgeneration.StringConstants;
import de.uka.ilkd.key.testgeneration.core.classabstraction.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.core.oracle.Oracle;
import de.uka.ilkd.key.testgeneration.core.oracle.OracleClause;
import de.uka.ilkd.key.testgeneration.core.oracle.OracleBooleanExpression;
import de.uka.ilkd.key.testgeneration.util.parsers.TermParserTools;
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

    /**
     * Separator to use when resolving {@link SortDependingFunction} instances.
     */
    private final String SEPARATOR = StringConstants.FIELD_SEPARATOR.toString();

    /**
     * Transformer used in order to transform {@link Term} instances
     * representing postconditions into a form suitable for turning them into
     * Oracles.
     */
    private final TermToOracleTransformer termToOracleTransformer = new TermToOracleTransformer(
            this.SEPARATOR);

    /**
     * Creates a Test Oracle for the provided method. The Oracle will be
     * generated based on the {@link FunctionalOperationContract} present for
     * the method, if any. If no such contract exists, a trivial Oracle is
     * generated with no inherent semantic value.
     * 
     * @param method
     *            the method
     * @return an Oracle for the method
     * @throws OracleGeneratorException
     */
    public Term createOracleForMethod(final KeYJavaMethod method)
            throws OracleGeneratorException {

        try {

            /*
             * Extract the postcondition of the method
             */
            final Term postCondition = method.getPostconditions().get(0);
            Term oracle;

            /*
             * Convert and return an Oracle corresponding to the postcondition.
             */
            oracle = this.termToOracleTransformer.transform(postCondition);

            return oracle;

        } catch (final TermTransformerException e) {

            throw new OracleGeneratorException(e.getMessage());
        }
    }
}