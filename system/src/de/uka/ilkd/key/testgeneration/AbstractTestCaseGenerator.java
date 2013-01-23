package de.uka.ilkd.key.testgeneration;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.keynterpol.EmbeddedModelGenerator;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.testgeneration.codecoverage.ICodeCoverageParser;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYInterface;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaClass;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaClassFactory;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.model.IModel;
import de.uka.ilkd.key.testgeneration.model.IModelGenerator;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.oraclegeneration.ContractExtractor;
import de.uka.ilkd.key.testgeneration.util.Benchmark;

public abstract class AbstractTestCaseGenerator implements ITestCaseGenerator {

    /**
     * A list of native methods (i.e. those part of any type with {@link Object}
     * as its supertype). We use this list in the event that we wish to ignore
     * such methods while generating test cases.
     */
    private static final LinkedList<String> nativeMethods = new LinkedList<String>();
    static {
        nativeMethods.add("equals");
        nativeMethods.add("toString");
        nativeMethods.add("wait");
        nativeMethods.add("notify");
        nativeMethods.add("notifyAll");
        nativeMethods.add("hashCode");
        nativeMethods.add("clone");
        nativeMethods.add("finalize");
    }

    /**
     * An instance of {@link IModelGenerator} for the purpose of generating
     * concrete fixtures for test cases. Default implementation based on SMT
     * solvers is available, but the user can choose to use her own.
     */
    protected final IModelGenerator modelGenerator;

    /**
     * Used in order to communicate with and request services from the KeY
     * runtime
     */
    protected final KeYInterface keYInterface = KeYInterface.INSTANCE;

    /**
     * Used in order to extract pre- and postconditions for methods
     */
    protected final ContractExtractor contractExtractor = ContractExtractor.INSTANCE;

    /**
     * Used in order to generate instances of {@link KeYJavaClass} for a given
     * source file
     */
    protected final KeYJavaClassFactory keYJavaClassFactory = KeYJavaClassFactory.INSTANCE;

    public AbstractTestCaseGenerator() {
        this(new EmbeddedModelGenerator());
    }
    
    public AbstractTestCaseGenerator(IModelGenerator modelGenerator) {
        this.modelGenerator = modelGenerator;
    }

    protected List<TestCase> generatePartialTestSuiteHelper(String source,
            ICodeCoverageParser codeCoverageParser, String... methods)
            throws TestGeneratorException {

        try {

            /*
             * Extract the abstract representations of the targeted Java class
             * and the specific method for which we wish to generate test cases.
             */
            Benchmark
                    .startBenchmarking("setting up class and method abstractions");
            KeYJavaClass targetClass = keYJavaClassFactory
                    .createKeYJavaClass(new File(source));

            List<TestCase> testCases = new LinkedList<TestCase>();

            for (String method : methods) {
                KeYJavaMethod targetMethod = targetClass.getMethod(method);

                Benchmark
                        .finishBenchmarking("setting up class and method abstractions");

                /*
                 * Retrieve the symbolic execution tree for the method, and
                 * extract from it the nodes needed in order to reach the
                 * desired level of code coverage.
                 */
                Benchmark.startBenchmarking("getting code coverage nodes");
                IExecutionStartNode root = keYInterface
                        .getSymbolicExecutionTree(targetMethod);
                List<IExecutionNode> targetNodes = codeCoverageParser
                        .retrieveNodes(root);
                Benchmark.finishBenchmarking("getting code coverage nodes");
                /*
                 * Extract the postcondition for the method, and generate test
                 * cases for each of the nodes.
                 */
                Benchmark.startBenchmarking("create test case abstractions");
                testCases.addAll(createTestCases(targetMethod, targetNodes));
                Benchmark.finishBenchmarking("create test case abstractions");
            }

            return testCases;

        } catch (KeYInterfaceException e) {
            throw new TestGeneratorException(e.getMessage());
        } catch (IOException e) {
            throw new TestGeneratorException(e.getMessage());
        }
    }

    /**
     * Creates a set of abstract test cases, represented by {@link TestCase},
     * for a given method.
     * 
     * @param method
     *            the method for which test cases will be generated
     * @param oracle
     *            the test oracle (corresponding to the postcondition) of the
     *            method
     * @param nodes
     *            the execution nodes (i.e. program statements) within the
     *            method itself for which to generate test cases (one test case
     *            per node will be generated)
     * @return a collection of {@link TestCase} instances for the method
     * @throws TestGeneratorException
     *             in the event there was a failure to generate a test case
     */
    protected List<TestCase> createTestCases(KeYJavaMethod method,
            List<IExecutionNode> nodes) throws TestGeneratorException {

        List<TestCase> testCases = new LinkedList<TestCase>();
        for (IExecutionNode node : nodes) {

            /*
             * FIXME: Very ugly workaround to safeguard against the model
             * failing...why does this happen?
             */
            Benchmark.startBenchmarking("   generating model "
                    + ++Benchmark.counters[0]);
            IModel model = null;
            while (model == null) {
                try {

                    model = modelGenerator.generateModel(node);
                } catch (ModelGeneratorException e) {
                    System.err.println("WARNING: Model generation failed!");
                }
            }
            Benchmark.finishBenchmarking("   generating model "
                    + Benchmark.counters[0]);

            /*
             * FIXME: This is an ugly hack since I am not sure how to handle
             * multiple postconditions yet, fix.
             */
            TestCase testCase = new TestCase(method, model, method
                    .getPostconditions().get(0));
            testCases.add(testCase);
        }
        return testCases;
    }
}
