package de.uka.ilkd.key.testgeneration.backend.junit;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.KeYTestGenMediator;
import de.uka.ilkd.key.testgeneration.backend.AbstractConcurrentTestCaseGenerator;
import de.uka.ilkd.key.testgeneration.backend.AbstractTestCaseGenerator;
import de.uka.ilkd.key.testgeneration.backend.ITestCaseGenerator;
import de.uka.ilkd.key.testgeneration.backend.TestCase;
import de.uka.ilkd.key.testgeneration.backend.TestGeneratorException;
import de.uka.ilkd.key.testgeneration.core.codecoverage.ICodeCoverageParser;
import de.uka.ilkd.key.testgeneration.core.codecoverage.implementation.StatementCoverageParser;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYJavaClass;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelGenerator;
import de.uka.ilkd.key.testgeneration.util.Benchmark;

/**
 * Instances of this implementation of {@link ITestCaseGenerator} generate test
 * suites for the JUnit4 framework.
 * 
 * @author christopher
 * 
 */
public class JUnitTestCaseGenerator extends AbstractConcurrentTestCaseGenerator {

    public JUnitTestCaseGenerator() throws ModelGeneratorException {
        super(ModelGenerator.getDefaultModelGenerator());
    }

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

        /*
         * Set up the mediator
         */
        KeYTestGenMediator mediator = new KeYTestGenMediator();

        /*
         * If no coverage criteria are specificed, use default.
         */
        if (coverage == null) {
            coverage = new StatementCoverageParser();
        }

        /*
         * Get the abstract representation of the class.
         */
        KeYJavaClass keYJavaClass = extractKeYJavaClass(source);
        mediator.setMainClass(keYJavaClass);
        
        /*
         * Get the abstract representations of the test cases for the selected
         * method(s).
         */
        LinkedList<TestCase> testCases = createTestCases(keYJavaClass,
                coverage, mediator, methods);

        /*
         * Turn the representations into JUnit sources.
         */
        Benchmark.startBenchmarking("create JUnit sources");
        JUnitGenerator jUnitGenerator = new JUnitGenerator();

        String testSuite = jUnitGenerator.generateJUnitSources(keYJavaClass,
                testCases);
        Benchmark.finishBenchmarking("create JUnit sources");

        return testSuite;
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