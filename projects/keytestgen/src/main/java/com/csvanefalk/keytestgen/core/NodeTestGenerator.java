package com.csvanefalk.keytestgen.core;

import com.csvanefalk.keytestgen.backend.FrameworkConverterException;
import com.csvanefalk.keytestgen.backend.IFrameworkConverter;
import com.csvanefalk.keytestgen.backend.ITestSuite;
import com.csvanefalk.keytestgen.backend.TestGeneratorException;
import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaClass;
import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaClassFactory;
import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaMethod;
import com.csvanefalk.keytestgen.core.concurrency.capsules.CapsuleController;
import com.csvanefalk.keytestgen.core.concurrency.capsules.CapsuleExecutor;
import com.csvanefalk.keytestgen.core.concurrency.capsules.ModelCapsule;
import com.csvanefalk.keytestgen.core.concurrency.capsules.OracleCapsule;
import com.csvanefalk.keytestgen.core.model.implementation.Model;
import com.csvanefalk.keytestgen.core.oracle.abstraction.Oracle;
import com.csvanefalk.keytestgen.core.testsuiteabstraction.TestCase;
import com.csvanefalk.keytestgen.core.testsuiteabstraction.TestSuite;
import com.csvanefalk.keytestgen.util.Benchmark;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

import java.util.LinkedList;
import java.util.List;

/**
 * Encapsulates logic needed to construct Test Suites directly from individual
 * {@link IExecutionNode} instances.
 *
 * @author christopher
 */
public class NodeTestGenerator {

    private static NodeTestGenerator instance = null;

    public static NodeTestGenerator getInstance() {
        if (NodeTestGenerator.instance == null) {
            NodeTestGenerator.instance = new NodeTestGenerator();
        }
        return NodeTestGenerator.instance;
    }

    private final CapsuleExecutor capsuleExecutor = CapsuleExecutor.getInstance();

    KeYJavaClassFactory factory = KeYJavaClassFactory.getInstance();

    private NodeTestGenerator() {

    }

    public ITestSuite constructTestSuiteFromNode(final IExecutionNode node,
                                                 final IFrameworkConverter frameworkConverter) throws TestGeneratorException {

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
            final CapsuleController<ModelCapsule> modelController = new CapsuleController<ModelCapsule>();
            final CapsuleController<OracleCapsule> oracleController = new CapsuleController<OracleCapsule>();

            final ModelCapsule modelGenerationCapsule = new ModelCapsule(node);
            modelController.addChild(modelGenerationCapsule);

            final OracleCapsule oracleGenerationCapsule = new OracleCapsule(targetMethod);
            oracleController.addChild(oracleGenerationCapsule);

            modelController.executeAndWait();
            oracleController.executeAndWait();

            /*
             * Collect the results
             */
            final Oracle oracle = oracleGenerationCapsule.getResult();
            final Model model = modelGenerationCapsule.getResult();

            /*
             * Construct the test cases.
             */
            final List<TestCase> testCases = new LinkedList<TestCase>();
            final TestCase testCase = TestCase.constructTestCase(targetMethod, model, oracle);
            testCases.add(testCase);

            Benchmark.finishBenchmarking("3. generating models");

            /*
             * Construct the test suite.
             */

            final TestSuite testSuite = TestSuite.constructTestSuite(targetMethod.getDeclaringClass(),
                                                                     targetMethod,
                                                                     testCases);

            /*
             * Convert to JUnit and return
             */
            final ITestSuite finalSuite = frameworkConverter.convert(testSuite);
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
     * @param node the node
     * @return
     */
    private IExecutionMethodCall getMethodCallNode(final IExecutionNode node) {

        if (node instanceof IExecutionMethodCall) {
            return (IExecutionMethodCall) node;
        } else {
            return getMethodCallNode(node.getParent());
        }
    }

    public void __DEBUG_DISPOSE() {
        instance = null;
    }
}
