package de.uka.ilkd.key.testgeneration;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Method;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.DefaultProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodSubsetPO;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYInterface;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaClass;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaClassFactory;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.model.IModel;
import de.uka.ilkd.key.testgeneration.model.IModelGenerator;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelGenerator;
import de.uka.ilkd.key.testgeneration.xml.XMLGenerator;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * The main API interface for the KeYTestGen2 test case generation system. Targets can be passed
 * either as entire source files or individual methods. An implementation of the <
 * {@code ITestCaseXMLParser} can be provided in order to generate test cases for a specific
 * framework. Otherwise, KTG will simply return the default XML representation of test cases as a
 * raw {@code String}.
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
     * Used in order to transform test case data into KeYTestGens internal XML format
     */
    private final XMLGenerator xmlWriter = XMLGenerator.INSTANCE;

    /**
     * Used in order to generate instances of {@link KeYJavaClass} for a given source file
     */
    private final KeYJavaClassFactory keYJavaClassFactory = KeYJavaClassFactory.INSTANCE;

    /**
     * Used in order to communicate with and request services from the KeY runtime
     */
    private final KeYInterface keYInterface = KeYInterface.INSTANCE;

    private TestCaseGenerator(IModelGenerator modelGenerator) {

        this.modelGenerator = modelGenerator;
    }

    /**
     * Creates a default instance of the TestCaseGenerator, using only in-house implementations of
     * the various modules.
     * 
     * @return a default instance of {@link TestCaseGenerator}
     * @throws ModelGeneratorException
     *             in the event that the model could not be sucessfully initialized
     */
    public static TestCaseGenerator getDefaultInstance() throws ModelGeneratorException {

        return new TestCaseGenerator(ModelGenerator.getDefaultModelGenerator());
    }

    /**
     * Creates an instance of the TestCaseGenerator, using a custom instance {@link IModelGenerator}
     * in order to generate test fixtures.
     * 
     * @param modelGenerator
     *            the custom instance of {@link IModelGenerator} to use
     * @return a new instance of {@link TestCaseGenerator}
     */
    public static TestCaseGenerator getCustomInstance(IModelGenerator modelGenerator) {

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
     * Retrieve all methods for a given class.
     * 
     * @param targetClass
     *            the class for which to retrieve methods
     * @param services
     *            services for this KeY session (see {@link Services})
     * @param includePrivateMethods
     *            also retrieve non-public methods?
     * @param includeNativeMethods
     *            also retrieve native methods?
     * @return
     */
    private List<IProgramMethod> extractMethodsFromClass(
            final KeYJavaType targetClass,
            final Services services,
            final boolean includePrivateMethods,
            final boolean includeNativeMethods) {

        LinkedList<IProgramMethod> methods = new LinkedList<IProgramMethod>();

        for (IProgramMethod method : services.getJavaInfo().getAllProgramMethods(
                targetClass)) {

            /*
             * Filter out all native methods
             */
            if (!includeNativeMethods && nativeMethods.contains(method.getFullName())) {
                continue;
            }

            /*
             * Filter out non-public methods
             */
            if (!includePrivateMethods && !method.isPublic()) {
                continue;
            }

            /*
             * Filter out implicit methods, i.e. <prepare>, <create> etc.
             */
            if (method.getFullName().startsWith("<")) {
                continue;
            }

            methods.add(method);
        }

        return methods;
    }

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
     * returned in KeYTestGen2:s standard XML format
     * 
     * @param sourcePath
     *            path to the source file to produce cases for
     * @param method
     *            the method to produce test cases for
     * @return
     */
    public String generateTestCase(String sourcePath, String method) {

        /*
         * Create a KeYJavaFile instance for the targeted file
         */
        KeYJavaClass keYJavaFile;

        return null;
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

    private KeYJavaType getMainClass(File java) {

        return null;
    }

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> createSymbolicExecutionEnvironment(
            File javaFile,
            IProgramMethod method,
            String precondition)
            throws ProofInputException, IOException, TestGeneratorException {

        try {

            /*
             * Set up the KeY user interface (here used only by the symbolic execution environment.
             */
            CustomConsoleUserInterface ui = new CustomConsoleUserInterface(false);

            /*
             * Load the Java file into KeY
             */
            DefaultProblemLoader loader = ui.load(javaFile, null, null);
            InitConfig initConfig = loader.getInitConfig();

            /*
             * Setup and prepare the proof session
             */
            ProofOblInput input =
                    new ProgramMethodPO(initConfig,
                            method.getFullName(),
                            method,
                            precondition,
                            true);
            Proof proof = ui.createProof(initConfig, input);

            assertNotNull(proof, "FATAL: unable to load proof");

            /*
             * Setup a strategy and goal chooser for the proof session
             */
            SymbolicExecutionEnvironment.configureProofForSymbolicExecution(
                    proof,
                    ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN);

            /*
             * Create the symbolic execution environment itself. Assert that it has been sucessfully
             * created.
             */
            SymbolicExecutionTreeBuilder builder =
                    new SymbolicExecutionTreeBuilder(ui.getMediator(), proof, false);

            SymbolicExecutionEnvironment<CustomConsoleUserInterface> env =
                    new SymbolicExecutionEnvironment<CustomConsoleUserInterface>(ui,
                            initConfig,
                            builder);

            assertNotNull(env,
                    "FATAL: unable to initialize symbolic execution environment");

            /*
             * Add a stop condition for the proof (we use a default in order to assure maximum
             * coverage of execution paths. Start the proof and wait for it to finish.
             */
            proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(
                    new ExecutedSymbolicExecutionTreeNodesStopCondition(ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN));

            env.getUi().startAndWaitForProof(proof);

            /*
             * Create the symbolic execution tree, and assert that it indeed exists.
             */
            builder.analyse();
            assertNotNull(builder.getStartNode(),
                    "FATAL: unable to initialize proof tree");

            /*
             * Finally, return the created environment.
             */
            return env;

        }
        catch (ProofInputException pe) {
            throw new TestGeneratorException("FATAL: unable to load proof: "
                    + pe.getMessage());
        }
        catch (IOException e) {
            throw new TestGeneratorException("FATAL: unable to load file: "
                    + e.getMessage());
        }
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

    private void assertNotNull(Object object, String failureMessage)
            throws TestGeneratorException {

        if (object == null) {
            throw new TestGeneratorException(failureMessage);
        }
    }
}