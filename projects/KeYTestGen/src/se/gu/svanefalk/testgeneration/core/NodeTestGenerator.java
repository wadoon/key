package se.gu.svanefalk.testgeneration.core;

import java.util.LinkedList;
import java.util.List;

import se.gu.svanefalk.testgeneration.backend.FrameworkConverterException;
import se.gu.svanefalk.testgeneration.backend.IFrameworkConverter;
import se.gu.svanefalk.testgeneration.backend.TestGeneratorException;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClass;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClassFactory;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaMethod;
import se.gu.svanefalk.testgeneration.core.concurrency.ModelGenerationCapsule;
import se.gu.svanefalk.testgeneration.core.concurrency.OracleGenerationCapsule;
import se.gu.svanefalk.testgeneration.core.model.implementation.Model;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.Oracle;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestCase;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestSuite;
import se.gu.svanefalk.testgeneration.util.Benchmark;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Encapsulates logic needed to construct Test Suites directly from individual
 * {@link IExecutionNode} instances.
 * 
 * @author christopher
 */
public enum NodeTestGenerator {
    INSTANCE;

    KeYJavaClassFactory factory = KeYJavaClassFactory.INSTANCE;

    public String constructTestSuiteFromNode(final IExecutionNode node,
            IFrameworkConverter frameworkConverter)
            throws TestGeneratorException {

        try {

            node.getMediator();

            /*
             * Get and process the method call node
             */
            final IExecutionMethodCall methodCall = this
                    .getMethodCallNode(node);

            String methodName = methodCall.getMethodReference().getName();

            /*
             * Construct the corresponding KeYJavaClass
             */
            KeYJavaClass keYJavaClass = factory.createKeYJavaClass(methodCall);
            KeYJavaMethod targetMethod = keYJavaClass.getMethod(methodName);

            /*
             * Create and dispatc the Model and Oracle geneators.
             */
            ModelGenerationCapsule modelGenerationCapsule = new ModelGenerationCapsule(
                    node);
            modelGenerationCapsule.start();

            OracleGenerationCapsule oracleGenerationCapsule = new OracleGenerationCapsule(
                    targetMethod);
            oracleGenerationCapsule.start();

            /*
             * Wait for them to finish.
             */
            while (true) {
                try {
                    oracleGenerationCapsule.join();
                    modelGenerationCapsule.join();
                    break;
                } catch (InterruptedException e) {
                    continue;
                }
            }

            /*
             * Collect the results
             */
            Oracle oracle = oracleGenerationCapsule.getResult();
            Model model = modelGenerationCapsule.getResult();

            /*
             * Construct the test cases.
             */
            List<TestCase> testCases = new LinkedList<TestCase>();
            TestCase testCase = TestCase.constructTestCase(targetMethod, model,
                    oracle);
            testCases.add(testCase);

            Benchmark.finishBenchmarking("3. generating models");

            /*
             * Construct the test suite.
             */

            TestSuite testSuite = TestSuite.constructTestSuite(
                    targetMethod.getDeclaringClass(), targetMethod, testCases);

            /*
             * Convert to JUnit and return
             */
            String finalSuite = frameworkConverter.convert(testSuite);
            return finalSuite;

        } catch (CoreException e) {
            throw new TestGeneratorException(e.getMessage());
        } catch (FrameworkConverterException e) {
            throw new TestGeneratorException(e.getMessage());
        }
    }

    /**
     * Given an {@link IExecutionNode} somewhere in a symbolic execution tree
     * and below the method call node, backtracks until the method call node is
     * found.
     * 
     * @param node
     *            the node
     * @return
     */
    private IExecutionMethodCall getMethodCallNode(final IExecutionNode node) {

        if (node instanceof IExecutionMethodCall) {
            return (IExecutionMethodCall) node;
        } else {
            return this.getMethodCallNode(node.getParent());
        }
    }
}
