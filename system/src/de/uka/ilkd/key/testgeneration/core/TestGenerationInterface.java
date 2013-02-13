package de.uka.ilkd.key.testgeneration.core;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.testgeneration.KeYTestGenMediator;
import de.uka.ilkd.key.testgeneration.backend.TestGeneratorException;
import de.uka.ilkd.key.testgeneration.core.codecoverage.ICodeCoverageParser;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterface;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.core.model.IModel;
import de.uka.ilkd.key.testgeneration.core.model.IModelGenerator;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelGenerator;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelMediator;
import de.uka.ilkd.key.testgeneration.core.oraclegeneration.ContractExtractor;
import de.uka.ilkd.key.testgeneration.util.Benchmark;

/**
 * Instances of this class provide a single interface between backend modules
 * and KeYTestGen itself, allowing them to request services related to test case
 * generation.
 * <p>
 * Backend modules should not be allowed to interact with KeYTestGen2 through
 * any other means than this singleton. TODO: Enforce this through access
 * restriction.
 * 
 * @author christopher
 * 
 */
public final class TestGenerationInterface {

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

    private TestGenerationInterface() {
        this(ModelGenerator.getDefaultModelGenerator());
    }

    public static TestGenerationInterface getDefaultTestGenerationInterface() {
        return new TestGenerationInterface();
    }

    /*
     * public static TestGenerationInterface getCustomTestGenerationInterface(
     * IModelGenerator modelGenerator) { return new
     * TestGenerationInterface(modelGenerator); }
     */

    /**
     * Creates a concurrent test case generator with a custom model generator.
     * 
     * @param modelGenerator
     */
    private TestGenerationInterface(ModelGenerator modelGenerator) {
        this.modelGenerator = modelGenerator;
    }

    /**
     * This helper method will construct a {@link KeYJavaClass} instance for the
     * public class in a given Java source file.
     * 
     * @param source
     *            path to the source file
     * @return a {@link KeYJavaClass} instance corresponding to the public class
     *         in the source file
     * @throws TestGeneratorException
     *             in the event that there is a failure in the KeYInterface, or
     *             if there is a problem finding or reading the source file.
     */
    public KeYJavaClass extractKeYJavaClass(String source)
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

    public LinkedList<TestCase> createTestCases(KeYJavaClass targetClass,
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
    private List<TestCase> createTestCasesForMethod(KeYJavaMethod method,
            KeYTestGenMediator mediator, List<IExecutionNode> nodes)
            throws TestGeneratorException {

        List<TestCase> testCases = new LinkedList<TestCase>();
        List<ModelCapsule> capsules = new LinkedList<ModelCapsule>();

        Benchmark.startBenchmarking("generating models");

        /*
         * Create the ModelMediator and initialize instance to be used in each
         * model generation session for the method we are generating test cases
         * for.
         */
        ModelMediator modelMediator = new ModelMediator();
        modelMediator.setMainClass(mediator.getMainClass());
        modelMediator.setMethod(method);
        LinkedList<String> methodParameters = new LinkedList<String>();
        for (IProgramVariable programVariable : method.getParameters()) {
            methodParameters.add(programVariable.name().toString());
        }
        modelMediator.setMethodParameterNames(methodParameters);

        try {

            /*
             * Setup the module generation capsules for each node.
             */
            for (IExecutionNode node : nodes) {
                ModelCapsule capsule = new ModelCapsule(node, modelMediator);
                capsules.add(capsule);
            }

            /*
             * Dispatch the capsules.
             */
            for (ModelCapsule capsule : capsules) {
                capsule.start();
            }

            /*
             * Finally, wait for the capsules to finsh their work, and collect
             * the results.
             */
            for (ModelCapsule capsule : capsules) {
                capsule.join();
                testCases.add(capsule.getResult());
            }

        } catch (InterruptedException ie) {
            System.err.println("INTERRUPTED!");
        }

        Benchmark.finishBenchmarking("generating models");

        return testCases;
    }

    /**
     * Instances of this class are used in order to enable concurrent model
     * generation for several nodes simultaneously.
     * 
     * @author christopher
     * 
     */
    private class ModelCapsule extends Thread {

        /**
         * The {@link IExecutionNode} instance associated with this capsule.
         */
        private final IExecutionNode node;

        /**
         * The {@link ModelMediator} instance assoicated with the model
         * generation session for this capsules node.
         */
        private final ModelMediator modelMediator;

        /**
         * The testCase generated by the model generation session executed by
         * this capsule.
         */
        TestCase testCase = null;

        public ModelCapsule(IExecutionNode node, ModelMediator modelMediator) {

            this.node = node;
            this.modelMediator = modelMediator;
        }

        /**
         * Generates a model for the node in this capsule, and creates a final
         * {@link TestCase} instance to encapsulate it.
         */
        @Override
        public void run() {

            IModel model = null;
            while (model == null) {

                try {

                    model = modelGenerator.generateModel(node, modelMediator);

                } catch (ModelGeneratorException e) {
                    System.err.println("WARNING: Model generation failed!");
                }
            }

            KeYJavaMethod method = modelMediator.getMethod();
            testCase = new TestCase(method, model, method.getPostconditions()
                    .get(0));
            testCase.setNode(node);
        }

        public TestCase getResult() {
            return testCase;
        }
    }
}