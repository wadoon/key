package se.gu.svanefalk.testgeneration.core;

import java.util.LinkedList;
import java.util.List;

import se.gu.svanefalk.testgeneration.backend.FrameworkConverterException;
import se.gu.svanefalk.testgeneration.backend.IFrameworkConverter;
import se.gu.svanefalk.testgeneration.backend.TestGeneratorException;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClass;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClassFactory;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaMethod;
import se.gu.svanefalk.testgeneration.core.concurrency.Capsule;
import se.gu.svanefalk.testgeneration.core.concurrency.CapsuleExecutor;
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

    private final CapsuleExecutor capsuleExecutor = CapsuleExecutor.INSTANCE;

    KeYJavaClassFactory factory = KeYJavaClassFactory.INSTANCE;

    public String constructTestSuiteFromNode(final IExecutionNode node,
            final IFrameworkConverter frameworkConverter)
            throws TestGeneratorException {

        try {

            /*
             * Get and process the method call node
             */
            final IExecutionMethodCall methodCall = getMethodCallNode(node);

            final String methodName = methodCall.getMethodReference().getName();

            /*
             * Construct the corresponding KeYJavaClass
             */
            final KeYJavaClass keYJavaClass = factory.createKeYJavaClass(methodCall);
            final KeYJavaMethod targetMethod = keYJavaClass.getMethod(methodName);

            /*
             * Create and dispatc the Model and Oracle geneators.
             */
            final List<Capsule> capsules = new LinkedList<Capsule>();
            final ModelGenerationCapsule modelGenerationCapsule = new ModelGenerationCapsule(
                    node);
            capsules.add(modelGenerationCapsule);

            final OracleGenerationCapsule oracleGenerationCapsule = new OracleGenerationCapsule(
                    targetMethod);
            capsules.add(oracleGenerationCapsule);

            capsuleExecutor.executeCapsulesAndWait(capsules);

            /*
             * Collect the results
             */
            final Oracle oracle = oracleGenerationCapsule.getResult();
            final Model model = modelGenerationCapsule.getResult();

            /*
             * Construct the test cases.
             */
            final List<TestCase> testCases = new LinkedList<TestCase>();
            final TestCase testCase = TestCase.constructTestCase(targetMethod,
                    model, oracle);
            testCases.add(testCase);

            Benchmark.finishBenchmarking("3. generating models");

            /*
             * Construct the test suite.
             */

            final TestSuite testSuite = TestSuite.constructTestSuite(
                    targetMethod.getDeclaringClass(), targetMethod, testCases);

            /*
             * Convert to JUnit and return
             */
            final String finalSuite = frameworkConverter.convert(testSuite);
            return finalSuite;

        } catch (final CoreException e) {
            throw new TestGeneratorException(e.getMessage());
        } catch (final FrameworkConverterException e) {
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
            return getMethodCallNode(node.getParent());
        }
    }
}
