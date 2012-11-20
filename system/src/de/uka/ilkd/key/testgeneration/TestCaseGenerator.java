package de.uka.ilkd.key.testgeneration;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.testgeneration.codecoverage.ICodeCoverageParser;
import de.uka.ilkd.key.testgeneration.codecoverage.implementation.StatementCoverageParser;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYInterface;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaClass;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaClassFactory;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.model.IModel;
import de.uka.ilkd.key.testgeneration.model.IModelGenerator;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelGenerator;
import de.uka.ilkd.key.testgeneration.oraclegeneration.ContractExtractor;
import de.uka.ilkd.key.testgeneration.xml.XMLGenerator;
import de.uka.ilkd.key.testgeneration.xml.XMLGeneratorException;

/**
 * Represents the main API interface for the KeYTestGen2. Targets can be passed either as entire
 * source files or individual methods. An implementation of the < {@code ITestCaseXMLParser} can be
 * provided in order to generate test cases for a specific framework. Otherwise, KTG will simply
 * return the default XML representation of test cases as a raw {@code String}.
 * 
 * @author christopher
 */
public class TestCaseGenerator {

    /**
     * A list of native methods (i.e. those part of any type with {@link Object} as its supertype).
     * We use this list in the event that we wish to ignore such methods while generating test
     * cases.
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
     * An instance of {@link IModelGenerator} for the purpose of generating concrete fixtures for
     * test cases. Default implementation based on SMT solvers is available, but the user can choose
     * to use her own.
     */
    private final IModelGenerator modelGenerator;

    /**
     * Used in order to communicate with and request services from the KeY runtime
     */
    private final KeYInterface keYInterface = KeYInterface.INSTANCE;

    /**
     * Used in order to extract pre- and postconditions for methods
     */
    private final ContractExtractor contractExtractor = ContractExtractor.INSTANCE;

    /**
     * Used in order to generate instances of {@link KeYJavaClass} for a given source file
     */
    private final KeYJavaClassFactory keYJavaClassFactory = KeYJavaClassFactory.INSTANCE;

    /**
     * Instances are generated through the {@link #getCustomInstance(IModelGenerator)} or
     * {@link #getDefaultInstance()} mehtods.
     * 
     * @param modelGenerator
     * @throws XMLGeneratorException
     */
    private TestCaseGenerator(IModelGenerator modelGenerator)
            throws XMLGeneratorException {

        this.modelGenerator = modelGenerator;

    }

    /**
     * Creates a default instance of the TestCaseGenerator, using only in-house implementations of
     * the various modules.
     * 
     * @return a default instance of {@link TestCaseGenerator}
     * @throws ModelGeneratorException
     *             in the event that the model could not be sucessfully initialized
     * @throws XMLGeneratorException
     */
    public static TestCaseGenerator getDefaultInstance()
            throws ModelGeneratorException, XMLGeneratorException {

        return new TestCaseGenerator(ModelGenerator.getDefaultModelGenerator());
    }

    /**
     * Creates an instance of the TestCaseGenerator, using a custom instance {@link IModelGenerator}
     * in order to generate test fixtures.
     * 
     * @param modelGenerator
     *            the custom instance of {@link IModelGenerator} to use
     * @return a new instance of {@link TestCaseGenerator}
     * @throws XMLGeneratorException
     */
    public static TestCaseGenerator getCustomInstance(IModelGenerator modelGenerator)
            throws XMLGeneratorException {

        return new TestCaseGenerator(modelGenerator);
    }

    public void test()
            throws IOException, ProofInputException, TestGeneratorException,
            KeYInterfaceException {

        KeYJavaClass javaFile =
                keYJavaClassFactory.createKeYJavaClass("/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java");
        KeYJavaMethod method = javaFile.getMethod("max");
        System.out.println(keYInterface.getSymbolicExecutionTree(method).getChildren()[0]);
        /*
         * File file = getJavaFile(
         * "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java"
         * );
         * 
         * CustomConsoleUserInterface ui = new CustomConsoleUserInterface(false);
         * DefaultProblemLoader loader = ui.load(file, null, null);
         * 
         * KeYMediator mediator = loader.getMediator(); InitConfig initConfig =
         * loader.getInitConfig(); Services services = initConfig.getServices(); JavaInfo javaInfo =
         * services.getJavaInfo();
         * 
         * InitConfig config = loader.getInitConfig();
         * 
         * KeYJavaType type = javaInfo.getKeYJavaTypeByClassName("PrimitiveIntegerOperations");
         * ImmutableList<Method> methods = javaInfo.getAllMethods(type);
         * 
         * for (IProgramMethod method : javaInfo.getAllProgramMethods(type)) {
         * System.out.println(method.getFullName()); }
         * 
         * for (IProgramMethod method : extractMethodsFromClass(type, services, false, false)) {
         * System.out.println("Prepping: "+ method.getFullName());
         * System.out.println(createSymbolicExecutionEnvironment(file, method,
         * null).getBuilder().getStartNode()); }
         */
    }

    /**
     * Generates a test case for a single {@link IExecutionNode} in a single method.
     * 
     * @param targetNode
     *            the target program node
     * @param services
     * @return
     * @throws Exception
     */
    private String generateTestCase(
            final IExecutionNode targetNode,
            final Services services) throws Exception {

        /*
         * Use the ModelGenerator in order to retrieve a model for the precondition
         */
        IModel model = modelGenerator.generateModel(targetNode);

        /*
         * Use the XML writer in order to generate an XML representation for the entire testcase
         */
        return null;
    }

    /**
     * Generate test cases for a specific method in the class being tested. The test cases will be
     * in the format specified by the provided {@link ITestCaseXMLParser}.
     * 
     * @param parser
     *            the parser to use to produce test cases
     * @param sourcePath
     *            path to the source file to produce cases for
     * @param method
     *            the method to produce test cases for
     * @return
     */
    public <T> T generateTestCase(
            ITestCaseParser<T> parser,
            String sourcePath,
            String method) {

        return null;
    }

    /**
     * Generate test cases for a specific method in the class being tested. The test case will be
     * returned in KeYTestGen2:s standard XML format. Uses a default level of code coverage.
     * 
     * @param sourcePath
     *            path to the source file to produce cases for
     * @param method
     *            the method to produce test cases for
     * @return
     * @throws TestGeneratorException
     *             in the event there was an error in creating the test case
     */
    public String generateTestCase(String sourcePath, String method)
            throws TestGeneratorException {

        return generateTestCase(sourcePath, method, new StatementCoverageParser());
    }

    /**
     * Generate test cases for a specific method in the class being tested. The test case will be
     * returned in KeYTestGen2:s standard XML format
     * 
     * @param sourcePath
     *            path to the source file to produce cases for
     * @param method
     *            the method to produce test cases for
     * @param codeCoverageParser
     *            the instance of {@link ICodeCoverageParser} to be used in order to achieve a
     *            desired degree of code coverage
     * @return
     * @throws TestGeneratorException
     *             in the event there was an error in creating the test cases
     */
    public String generateTestCase(
            String sourcePath,
            String method,
            ICodeCoverageParser codeCoverageParser) throws TestGeneratorException {

        try {

            /*
             * Extract the abstract representations of the targeted Java class and the specific
             * method for which we wish to generate test cases.
             */
            KeYJavaClass targetClass = keYJavaClassFactory.createKeYJavaClass(sourcePath);
            KeYJavaMethod targetMethod = targetClass.getMethod(method);

            /*
             * Retrieve the symbolic execution tree for the method, and extract from it the nodes
             * needed in order to reach the desired level of code coverage.
             */
            IExecutionStartNode root =
                    keYInterface.getSymbolicExecutionTree(targetMethod);
            List<IExecutionNode> targetNodes = codeCoverageParser.retrieveNodes(root);

            /*
             * Extract the postcondition for the method, and generate test cases for each of the
             * nodes.
             */
            List<TestCase> testCases = createTestCases(targetMethod, targetNodes);

            /*
             * Create and return a final XML representation of the test suite.
             */
            XMLGenerator xmlWriter = new XMLGenerator();
            return xmlWriter.createTestSuite(testCases, true);
        }
        catch (KeYInterfaceException e) {
            throw new TestGeneratorException(e.getMessage());
        }
        catch (IOException e) {
            throw new TestGeneratorException(e.getMessage());
        }
        catch (XMLGeneratorException e) {
            throw new TestGeneratorException(e.getMessage());
        }
    }

    /**
     * Generate test cases for all methods in the class being tested. The test cases will be in the
     * format specified by the provided {@link ITestCaseXMLParser}.
     * 
     * @param parser
     *            the parser to use to produce test cases
     * @param sourcePath
     *            path to the source file to produce cases for
     * @param includePrivateMethods
     *            also generate test cases for private methods?
     * @return
     */
    public <T> T generateTestCases(
            ITestCaseParser<T> parser,
            String sourcePath,
            boolean includePrivateMethods) {

        return null;
    }

    /**
     * Generate test cases for all methods in the class being tested. The test cases will be
     * returned in the XML format generated by KeYTestGen2.
     * 
     * @param sourcePath
     *            path to the source file to produce cases for
     * @param includeNonPublicMethods
     *            also generate test cases for private methods?
     * @param includeNativeMethods
     *            include native methods (equals, toString etc)?
     * @return
     * @throws TestGeneratorException
     */
    public List<String> generateTestCases(
            String sourcePath,
            boolean includeNonPublicMethods,
            boolean includeNativeMethods) throws TestGeneratorException {

        File javaFile = getJavaFile(sourcePath);

        // List<IProgramMethod> methods = extractMethodsFromClass(targetClass, services,
        // includePrivateMethods, includeNativeMethods)

        return null;
    }

    /**
     * Creates a set of abstract test cases, represented by {@link TestCase}, for a given method.
     * 
     * @param method
     *            the method for which test cases will be generated
     * @param oracle
     *            the test oracle (corresponding to the postcondition) of the method
     * @param nodes
     *            the execution nodes (i.e. program statements) within the method itself for which
     *            to generate test cases (one test case per node will be generated)
     * @return a collection of {@link TestCase} instances for the method
     * @throws TestGeneratorException
     *             in the event there was a failure to generate a test case
     */
    private List<TestCase> createTestCases(
            KeYJavaMethod method,
            List<IExecutionNode> nodes) throws TestGeneratorException {

        List<TestCase> testCases = new LinkedList<TestCase>();
        for (IExecutionNode node : nodes) {

            /*
             * FIXME: Very ugly workaround to safeguard against the model failing...why does this
             * happen?
             */
            IModel model = null;
            while (model == null) {
                try {
                    model = modelGenerator.generateModel(node);
                }
                catch (ModelGeneratorException e) {
                    System.err.println("WARNING: Model generation failed!");
                }
            }

            /*
             * FIXME: This is an ugly hack since I am not sure how to handle multiple postconditions
             * yet, fix.
             */
            TestCase testCase =
                    new TestCase(method, model, method.getPostconditions().get(0));
            testCases.add(testCase);
        }
        return testCases;
    }

    /**
     * Retrieve a {@link File} reference to the .java file selected by the user.
     * 
     * @param path
     * @return
     * @throws TestGeneratorException
     */
    private File getJavaFile(String path) throws TestGeneratorException {

        File javaFile = new File(path);
        if (!javaFile.exists()) {
            throw new TestGeneratorException("FATAL: no such file or directory: " + path);
        }
        return javaFile;
    }
}