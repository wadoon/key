package de.uka.ilkd.key.testgeneration.backend.junit.abstraction;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.core.oraclegeneration.PostconditionTools;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.TermTransformerException;
import junit.framework.Assert;

/**
 * Instances of this class represent JUnit test cases, i.e. methods annotated
 * with @Test.
 * <p>
 * It consists of a test fixture, an execution of the method under test (with a
 * possible storage of the result, if the method is non-void), and a subsequent
 * set of {@link Assert#assertTrue(boolean)} invocations in order to verify the
 * post-state.
 * 
 * @author christopher
 * 
 */
public class JUnitTestCase {

    /**
     * The method which this test case is testing.
     */

    /**
     * The fixture for this test case.
     */
    private final JUnitFixture fixture = new JUnitFixture();

    /**
     * The postcondition ("oracle") for the Term. Left raw for now.
     */
    private final Term oracle;

    public JUnitTestCase(Term postCondition) throws TermTransformerException {

        Term simplifiedPostcondition = PostconditionTools
                .simplifyPostCondition(postCondition, "_");

        Term cnf_postCondition = simplifiedPostcondition;
        
        this.oracle = cnf_postCondition;
    }
}
