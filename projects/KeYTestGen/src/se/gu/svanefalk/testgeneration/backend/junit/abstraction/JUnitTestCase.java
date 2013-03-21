package se.gu.svanefalk.testgeneration.backend.junit.abstraction;

import junit.framework.Assert;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestCase;

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
     * The fixture for this test case.
     */
    private final JUnitFixture fixture = new JUnitFixture();

    public JUnitTestCase(final TestCase testCase) {

        assert testCase != null;
    }
}