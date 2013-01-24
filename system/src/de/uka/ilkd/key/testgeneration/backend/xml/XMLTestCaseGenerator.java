package de.uka.ilkd.key.testgeneration.backend.xml;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.backend.AbstractTestCaseGenerator;
import de.uka.ilkd.key.testgeneration.backend.ITestCaseGenerator;
import de.uka.ilkd.key.testgeneration.backend.TestCase;
import de.uka.ilkd.key.testgeneration.backend.TestGeneratorException;
import de.uka.ilkd.key.testgeneration.codecoverage.ICodeCoverageParser;
import de.uka.ilkd.key.testgeneration.codecoverage.implementation.StatementCoverageParser;
import de.uka.ilkd.key.testgeneration.model.IModelGenerator;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelGenerator;
import de.uka.ilkd.key.testgeneration.util.Benchmark;
import de.uka.ilkd.key.testgeneration.xml.XMLGeneratorException;
import de.uka.ilkd.key.testgeneration.xmlparser.ITestCaseParser;

/**
 * This implementation of {@link ITestCaseGenerator} generates test suites in
 * KeYTestGen2s XML metalanguage. Such test suites can be processed by instances
 * of {@link ITestCaseParser} in order to covert them to specific test
 * frameworks.
 * 
 * @author christopher
 */
public class XMLTestCaseGenerator extends AbstractTestCaseGenerator {

    /**
     * Instances are generated through the
     * {@link #getCustomInstance(IModelGenerator)} or
     * {@link #getDefaultInstance()} mehtods.
     * 
     * @param modelGenerator
     * @throws XMLGeneratorException
     */
    public XMLTestCaseGenerator(IModelGenerator modelGenerator)
            throws XMLGeneratorException {

        super(modelGenerator);
    }

    /**
     * Creates a default instance of the XMLTestCaseGenerator, using only
     * in-house implementations of the various modules.
     * 
     * @return a default instance of {@link XMLTestCaseGenerator}
     * @throws ModelGeneratorException
     *             in the event that the model could not be sucessfully
     *             initialized
     * @throws XMLGeneratorException
     */
    public static XMLTestCaseGenerator getDefaultInstance()
            throws ModelGeneratorException, XMLGeneratorException {

        return new XMLTestCaseGenerator(
                ModelGenerator.getDefaultModelGenerator());
    }

    /**
     * Creates an instance of the XMLTestCaseGenerator, using a custom instance
     * {@link IModelGenerator} in order to generate test fixtures.
     * 
     * @param modelGenerator
     *            the custom instance of {@link IModelGenerator} to use
     * @return a new instance of {@link XMLTestCaseGenerator}
     * @throws XMLGeneratorException
     */
    public static XMLTestCaseGenerator getCustomInstance(
            IModelGenerator modelGenerator) throws XMLGeneratorException {

        return new XMLTestCaseGenerator(modelGenerator);
    }

    /*
     * public void test() throws IOException, ProofInputException,
     * TestGeneratorException, KeYInterfaceException {
     * 
     * KeYJavaClass javaFile = keYJavaClassFactory.createKeYJavaClass(
     * "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java"
     * ); KeYJavaMethod method = javaFile.getMethod("max");
     * System.out.println(keYInterface
     * .getSymbolicExecutionTree(method).getChildren()[0]);
     * 
     * File file = getJavaFile(
     * "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java"
     * );
     * 
     * CustomConsoleUserInterface ui = new CustomConsoleUserInterface(false);
     * DefaultProblemLoader loader = ui.load(file, null, null);
     * 
     * KeYMediator mediator = loader.getMediator(); InitConfig initConfig =
     * loader.getInitConfig(); Services services = initConfig.getServices();
     * JavaInfo javaInfo = services.getJavaInfo();
     * 
     * InitConfig config = loader.getInitConfig();
     * 
     * KeYJavaType type =
     * javaInfo.getKeYJavaTypeByClassName("PrimitiveIntegerOperations");
     * ImmutableList<Method> methods = javaInfo.getAllMethods(type);
     * 
     * for (IProgramMethod method : javaInfo.getAllProgramMethods(type)) {
     * System.out.println(method.getFullName()); }
     * 
     * for (IProgramMethod method : extractMethodsFromClass(type, services,
     * false, false)) { System.out.println("Prepping: "+ method.getFullName());
     * System.out.println(createSymbolicExecutionEnvironment(file, method,
     * null).getBuilder().getStartNode()); } }
     */

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

        try {

            if(coverage == null) {
                coverage = new StatementCoverageParser();
            }
            
            List<TestCase> testCases = generatePartialTestSuiteHelper(source,
                    coverage, methods);

            /*
             * Create and return a final XML representation of the test suite.
             */
            Benchmark.startBenchmarking("write XML");
            XMLGenerator xmlWriter = new XMLGenerator();

            String testSuite = xmlWriter.createTestSuite(testCases, true);
            Benchmark.finishBenchmarking("write XML");

            return testSuite;

        } catch (XMLGeneratorException e) {

            throw new TestGeneratorException(e.getMessage());
        }
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