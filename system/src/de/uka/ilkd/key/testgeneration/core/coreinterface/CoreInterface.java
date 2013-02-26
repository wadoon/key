package de.uka.ilkd.key.testgeneration.core.coreinterface;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.testgeneration.KeYTestGenMediator;
import de.uka.ilkd.key.testgeneration.backend.TestGeneratorException;
import de.uka.ilkd.key.testgeneration.core.KeYJavaClass;
import de.uka.ilkd.key.testgeneration.core.KeYJavaClassFactory;
import de.uka.ilkd.key.testgeneration.core.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.core.codecoverage.ICodeCoverageParser;
import de.uka.ilkd.key.testgeneration.core.codecoverage.implementation.StatementCoverageParser;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterface;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.core.model.IModel;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.core.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelGenerator;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelMediator;
import de.uka.ilkd.key.testgeneration.core.model.tools.ModelGenerationTools;
import de.uka.ilkd.key.testgeneration.core.oraclegeneration.ContractExtractor;
import de.uka.ilkd.key.testgeneration.core.oraclegeneration.OracleGenerationTools;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.ConjunctionNormalFormTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.SimplifyConjunctionTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.SimplifyDisjunctionTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.TermTransformerException;
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
public enum CoreInterface {
    INSTANCE;
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
    protected final ModelGenerator modelGenerator = ModelGenerator
            .getDefaultModelGenerator();

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
    private KeYJavaClass extractKeYJavaClass(final String source)
            throws CoreInterfaceException {

        try {

            /*
             * Extract the abstract representations of the targeted Java class
             * and the specific method for which we wish to generate test cases.
             */
            Benchmark
                    .startBenchmarking("1. [KeY] setting up class and method abstractions");

            KeYJavaClass keYJavaClass = keYJavaClassFactory
                    .createKeYJavaClass(new File(source));

            Benchmark
                    .finishBenchmarking("1. [KeY] setting up class and method abstractions");

            return keYJavaClass;

        } catch (KeYInterfaceException e) {
            throw new CoreInterfaceException(e.getMessage());
        } catch (IOException e) {
            throw new CoreInterfaceException(e.getMessage());
        }
    }

    public TestSuite createTestSuite(final String path,
            final String methodName, ICodeCoverageParser codeCoverageParser)
            throws CoreInterfaceException {

        /*
         * If no coverage criteria are specificed, use default.
         */
        if (codeCoverageParser == null) {
            codeCoverageParser = new StatementCoverageParser();
        }

        /*
         * Get the abstract representation of the class.
         */
        KeYJavaClass keYJavaClass = extractKeYJavaClass(path);

        /*
         * Internally generate and return the test suite for the class.
         */
        return createTestSuite(keYJavaClass, codeCoverageParser, methodName);
    }

    private TestSuite createTestSuite(final KeYJavaClass targetClass,
            final ICodeCoverageParser codeCoverageParser,
            final String methodName) throws CoreInterfaceException {

        try {

            KeYJavaMethod targetMethod = targetClass.getMethod(methodName);

            /*
             * Retrieve the symbolic execution tree for the method, and extract
             * from it the nodes needed in order to reach the desired level of
             * code coverage.
             */
            Benchmark.startBenchmarking("2. [KeY] Create symbolic execution tree");
            IExecutionStartNode root = keYInterface
                    .getSymbolicExecutionTree(targetMethod);

            List<IExecutionNode> targetNodes = codeCoverageParser
                    .retrieveNodes(root);
            Benchmark.finishBenchmarking("2. [KeY] Create symbolic execution tree");

            /*
             * Extract the postcondition for the method, and generate test cases
             * for each of the nodes.
             */
            //Benchmark.startBenchmarking("Create abstract test cases");
            List<TestCase> testCases = createTestCasesForMethod(targetClass,
                    targetMethod, targetNodes);
            //Benchmark.finishBenchmarking("Create abstract test cases");

            return new TestSuite(targetClass, targetMethod, testCases);

        } catch (KeYInterfaceException e) {
            throw new CoreInterfaceException(e.getMessage());
        }
    }

    public List<TestSuite> createTestSuites(final String path,
            final ICodeCoverageParser codeCoverageParser, String... methods)
            throws CoreInterfaceException {

        List<TestSuite> testSuites = new LinkedList<TestSuite>();
        for (String method : methods) {

            TestSuite testSuite = createTestSuite(path, method,
                    codeCoverageParser);
            testSuites.add(testSuite);
        }
        return testSuites;
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
     * @throws CoreInterfaceException
     */
    private List<TestCase> createTestCasesForMethod(
            final KeYJavaClass declaringClass, final KeYJavaMethod method,
            final List<IExecutionNode> nodes) throws CoreInterfaceException {

        /*
         * The generated test cases.
         */
        List<TestCase> testCases = new LinkedList<TestCase>();

        /*
         * The generated models.
         */
        List<Model> models = new LinkedList<Model>();

        /*
         * Capsules to run concurrent model generation sessions.
         */
        List<ModelCapsule> capsules = new LinkedList<ModelCapsule>();

        /*
         * The oracle for the method which the test cases are being generated
         * for.
         */
        Term oracle = null;

        Benchmark.startBenchmarking("3. generating models");

        /*
         * Create the ModelMediator and initialize instance to be used in each
         * model generation session for the method we are generating test cases
         * for.
         */
        ModelMediator modelMediator = new ModelMediator();
        modelMediator.setMainClass(declaringClass);
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
                
                /*
                try {
                    System.out.println(node.getFormatedPathCondition() + "\n\n");
                } catch (ProofInputException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }*/
                
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
                models.add(capsule.getResult());
            }

            /*
             * Generate the oracle for the method. TODO: Support multiple
             * contracts.
             */
            Term postcondition = method.getPostconditions().get(0);
            oracle = OracleGenerationTools.termToOracle(postcondition);

        } catch (InterruptedException ie) {

            throw new CoreInterfaceException(ie.getMessage());

        } catch (TermTransformerException tte) {

            throw new CoreInterfaceException(tte.getMessage());
        }

        /*
         * Construct and return the test cases.
         */
        for (Model model : models) {
            TestCase testCase = new TestCase(method, model, oracle);
            testCases.add(testCase);
        }

        Benchmark.finishBenchmarking("3. generating models");

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
         * The model generated by the session owned by this capsule.
         */
        Model model = null;

        public ModelCapsule(final IExecutionNode node,
                final ModelMediator modelMediator) {

            this.node = node;
            this.modelMediator = modelMediator;
        }

        /**
         * Generates a model for the node in this capsule, and creates a final
         * {@link TestCase} instance to encapsulate it.
         */
        @Override
        public void run() {

            while (model == null) {

                try {

                    model = modelGenerator.generateModel(node, modelMediator);

                } catch (ModelGeneratorException e) {
                    System.err.println(e.getMessage());
                    break;
                }
            }
        }

        public Model getResult() {
            return model;
        }
    }
}