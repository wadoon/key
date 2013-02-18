package de.uka.ilkd.key.testgeneration.backend.testNG;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.backend.AbstractTestCaseGenerator;
import de.uka.ilkd.key.testgeneration.backend.INodeTestCaseGenerator;
import de.uka.ilkd.key.testgeneration.backend.ITestCaseGenerator;
import de.uka.ilkd.key.testgeneration.backend.TestGeneratorException;
import de.uka.ilkd.key.testgeneration.core.codecoverage.ICodeCoverageParser;
import de.uka.ilkd.key.testgeneration.core.coreinterface.CoreInterface;

/**
 * Instances of this implementation of {@link ITestCaseGenerator} generate test
 * suites for the TestNG framework.
 * 
 * @author christopher
 * 
 */
public class TestNGTestCaseGenerator implements ITestCaseGenerator,
        INodeTestCaseGenerator {

    /**
     * KeYTestGen services for this test generation session.
     */
    CoreInterface testGenerationInterface = CoreInterface
            .getDefaultTestGenerationInterface();

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
