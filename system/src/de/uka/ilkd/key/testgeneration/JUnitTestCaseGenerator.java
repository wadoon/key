package de.uka.ilkd.key.testgeneration;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.codecoverage.ICodeCoverageParser;

/**
 * Instances of this implementation of {@link ITestCaseGenerator} generate test
 * suites for the JUnit4 framework.
 * 
 * @author christopher
 * 
 */
public class JUnitTestCaseGenerator extends AbstractTestCaseGenerator {

    /**
     * {@inheritDoc}
     */
    @Override
    public String generateTestCase(IExecutionNode targetNode, Services services)
            throws TestGeneratorException {
        // TODO Auto-generated method stub
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String generatePartialTestSuite(String source,
            ICodeCoverageParser coverage, String... methods)
            throws TestGeneratorException {
        // TODO Auto-generated method stub
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String generateFullTestSuite(String source,
            ICodeCoverageParser coverage, boolean includeProtected,
            boolean includePrivate, boolean includeNative)
            throws TestGeneratorException {
        // TODO Auto-generated method stub
        return null;
    }
}