package de.uka.ilkd.key.testgeneration.core.oraclegeneration;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.testgeneration.StringConstants;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.CNFTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.SimplifyConjunctionTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.SimplifyDisjunctionTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.TermTransformerException;

/**
 * Contains various methods related to processing the postconditions of methods
 * in Java files.
 * 
 * @author christopher
 */
public class OracleGenerationTools {

    private static final String SEPARATOR = StringConstants.FIELD_SEPARATOR
            .toString();

    /**
     * Transforms a Term into an equivalent Term representing an Oracle. The
     * semantics of the Term remain unchanged.
     * 
     * @param term
     * @return
     * @throws TermTransformerException
     */
    public static Term termToOracle(Term term) throws TermTransformerException {

        /*
         * Simplify the postcondition
         */
        Term simplifiedOracle = OracleGenerationTools.simplifyPostCondition(
                term, SEPARATOR);

        /*
         * Put it into Conjunctive Normal Form
         */
        simplifiedOracle = new CNFTransformer().transform(simplifiedOracle);

        /*
         * Simplify the disjunctions in the postcondition
         */
        simplifiedOracle = new SimplifyDisjunctionTransformer()
                .transform(simplifiedOracle);

        /*
         * Simplify the remaining conjunctions
         */
        simplifiedOracle = new SimplifyConjunctionTransformer()
                .transform(simplifiedOracle);

        return simplifiedOracle;
    }

    /**
     * Simplifies a postCondition, removing {@link SortDependingFunction} and
     * {@link ObserverFunction} instances.
     * 
     * @param term
     *            the term to simplify
     * @param separator
     *            separator do be used for constructing names for
     *            {@link SortDependingFunction} resolution.
     * @return the simplified postcondition
     * @throws TermTransformerException
     */
    public static Term simplifyPostCondition(Term term, String separator)
            throws TermTransformerException {

        return new TermToOracleConverter(separator).transform(term);
    }
}
