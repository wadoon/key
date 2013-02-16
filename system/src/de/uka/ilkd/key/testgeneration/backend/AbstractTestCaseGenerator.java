package de.uka.ilkd.key.testgeneration.backend;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.testgeneration.KeYTestGenMediator;
import de.uka.ilkd.key.testgeneration.core.KeYJavaClass;
import de.uka.ilkd.key.testgeneration.core.KeYJavaClassFactory;
import de.uka.ilkd.key.testgeneration.core.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.core.codecoverage.ICodeCoverageParser;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterface;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.core.model.IModel;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelGenerator;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelMediator;
import de.uka.ilkd.key.testgeneration.core.oraclegeneration.ContractExtractor;
import de.uka.ilkd.key.testgeneration.core.testgeneratorinterface.TestCase;
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
     * An instance of {@link ModelGenerator} for the purpose of generating
     * concrete fixtures for test cases. Default implementation based on SMT
     * solvers is available, but the user can choose to use her own.
     */
    protected final ModelGenerator modelGenerator;

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
        this(ModelGenerator.getDefaultModelGenerator());
    }

    public AbstractTestCaseGenerator(ModelGenerator modelGenerator) {
        this.modelGenerator = modelGenerator;
    }

    protected KeYJavaClass extractKeYJavaClass(String source)
            throws TestGeneratorException {

        try {

            /*
             * Extract the abstract representations of the targeted Java class
             * and the specific method for which we wish to generate test cases.
             */
            Benchmark
                    .startBenchmarking("setting up class and method abstractions");

            KeYJavaClass keYJavaClass = keYJavaClassFactory
                    .createKeYJavaClass(new File(source));

            Benchmark
                    .finishBenchmarking("setting up class and method abstractions");

            return keYJavaClass;

        } catch (KeYInterfaceException e) {
            throw new TestGeneratorException(e.getMessage());
        } catch (IOException e) {
            throw new TestGeneratorException(e.getMessage());
        }

    }

    protected LinkedList<TestCase> createTestCases(KeYJavaClass targetClass,
            ICodeCoverageParser codeCoverageParser,
            KeYTestGenMediator mediator, String... methods)
            throws TestGeneratorException {

        try {

            LinkedList<TestCase> testCases = new LinkedList<TestCase>();

            for (String method : methods) {
                KeYJavaMethod targetMethod = targetClass.getMethod(method);

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
                testCases.addAll(createTestCasesForMethod(targetMethod,
                        mediator, targetNodes));
                Benchmark.finishBenchmarking("create test case abstractions");
            }

            return testCases;

        } catch (KeYInterfaceException e) {
            throw new TestGeneratorException(e.getMessage());
        }
    }

    /**
     * Creates a set of abstract test cases, represented by {@link TestCase},
     * for a given method.
     * 
     * @param method
     *            the method for which test cases will be generated
     * @param mediator
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
    protected List<TestCase> createTestCasesForMethod(KeYJavaMethod method,
            KeYTestGenMediator mediator, List<IExecutionNode> nodes)
            throws TestGeneratorException {

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

                    /*
                     * Set up a temporary ModelMediator for use with this
                     * particular node.
                     */
                    ModelMediator modelMediator = new ModelMediator();
                    modelMediator.setMainClass(mediator.getMainClass());

                    /*
                     * Extract the method parameter names, to be passed to the
                     * model generator as part of the mediator.
                     */
                    LinkedList<String> methodParameters = new LinkedList<String>();
                    for (IProgramVariable programVariable : method
                            .getParameters()) {
                        methodParameters.add(programVariable.name().toString());
                    }
                    modelMediator.setMethodParameterNames(methodParameters);

                    /*
                     * Start the model generation session.
                     */
                    try {
                        System.out.println(node.getFormatedPathCondition());
                        System.out.println(node.getPathCondition().toString());
                    } catch (Exception e) {
                        
                    }
                    model = modelGenerator.generateModel(node, modelMediator);

                } catch (ModelGeneratorException e) {
                    System.err.println("WARNING: Model generation failed!");
                }
            }
            Benchmark.finishBenchmarking("   generating model "
                    + Benchmark.counters[0]);

            /*
             * Finally, encapsulate the metadata for the method together with
             * the newly generated model, as a final TestCase instance.
             */
            TestCase testCase = new TestCase(method, model, method
                    .getPostconditions().get(0));
            testCase.setNode(node); // Debug
            testCases.add(testCase);
        }
        return testCases;
    }
}
