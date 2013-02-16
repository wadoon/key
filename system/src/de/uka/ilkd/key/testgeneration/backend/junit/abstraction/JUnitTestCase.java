package de.uka.ilkd.key.testgeneration.backend.junit.abstraction;

import junit.framework.Assert;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.testgeneration.core.oraclegeneration.PostconditionTools;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.TermTransformerException;
import de.uka.ilkd.key.testgeneration.core.testgeneratorinterface.TestCase;

/**
 * Instances of this class represent JUnit test cases, i.e. methods annotated
 * with @Test.
 * <p>
 * It wraps a {@link TestCase} instance, and consists of a test fixture, an
 * execution of the method under test (with a possible storage of the result, if
 * the method is non-void), and a subsequent set of
 * {@link Assert#assertTrue(boolean)} invocations in order to verify the
 * post-state.
 * 
 * @author christopher
 * 
 */
public class JUnitTestCase {

    /**
     * The TestCase instance wrapped by this JUnitTestCase
     */
    private TestCase wrappedTestCase;

    /**
     * The fixture for this test case.
     */
    private final JUnitFixture fixture = new JUnitFixture();

    /**
     * The postcondition ("oracle") for the Term. Left raw for now.
     */
    private Term oracle;

    public JUnitTestCase(TestCase testCase) {

        assert (testCase != null);
        this.wrappedTestCase = wrappedTestCase;
    }

    /**
     * Returns the oracle for the test case, simplified and in conjunctive
     * normal form.
     * 
     * @return
     * @throws TermTransformerException
     */
    public Term getSimplifiedOracle() throws TermTransformerException {

        /*
         * Lazily instantiate the oracle Term
         */
        if (oracle == null) {

            Term simplifiedPostcondition = PostconditionTools
                    .simplifyPostCondition(wrappedTestCase.getOracle(), "_");

            Term cnf_postCondition = simplifiedPostcondition;
        }

        return oracle;
    }
}
