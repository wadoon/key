package se.gu.svanefalk.testgeneration.backend;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import se.gu.svanefalk.testgeneration.core.CoreException;
import se.gu.svanefalk.testgeneration.core.CoreInterface;
import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestSuite;
import se.gu.svanefalk.testgeneration.util.Benchmark;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * This singleton represents the principal API of KeYTestGen2. It supports the
 * following modes of operation:
 * <ul>
 * <li>Generate a test suite only for a subset case methods in a class.</li>
 * <li>Generate a test suite for all methods in a class, with the option of
 * including protected, private and methods inherited from
 * <code>java.lang.Object</code>.</li>
 * <li>Generate a test suite only for a single {@link IExecutionNode}.</li>
 * </ul>
 * For any of the options above the user can supply an implementation of
 * {@link IFrameworkConverter} in order to specify in what format the resulting
 * test suite(s) should be returned. If none is supplied (i.e. if the parameter
 * is <code>null</code>), then KeYTestGen2 will use its internal XML format by
 * default.
 * <p>
 * For any of the options above, the user has the option deciding the level of
 * code coverage to be provided, by supplying an instance of
 * {@link ICodeCoverageParser}. By default. Statement Coverage should be
 * targeted.
 * 
 * @author christopher
 * 
 */
public class TestGenerator {

    private static TestGenerator instance = null;

    public static TestGenerator getInstance() {
        if (TestGenerator.instance == null) {
            TestGenerator.instance = new TestGenerator();
        }
        return TestGenerator.instance;
    }

    /**
     * A list of native methods (i.e. those part of any type with {@link Object}
     * as its supertype). We use this list in the event that we wish to ignore
     * such methods while generating test cases.
     */
    private static final LinkedList<String> nativeMethods = new LinkedList<String>();

    static {
        TestGenerator.nativeMethods.add("equals");
        TestGenerator.nativeMethods.add("toString");
        TestGenerator.nativeMethods.add("wait");
        TestGenerator.nativeMethods.add("notify");
        TestGenerator.nativeMethods.add("notifyAll");
        TestGenerator.nativeMethods.add("hashCodeCore");
        TestGenerator.nativeMethods.add("clone");
        TestGenerator.nativeMethods.add("finalize");
    }
    /**
     * Interface to the KeYTestGen2 Core system.
     */
    private final CoreInterface coreInterface = CoreInterface.getInstance();

    /**
     * Generates a set of JUnit test cases for each method in a Java source
     * file, according to the users preferences.
     * 
     * @param source
     *            path to the Java source file.
     * @param coverage
     *            code coverage critera to be satisfied by the generated test
     *            cases. May be <code>null</code>, in which case a default
     *            statement coverage is used.
     * @param includeProtected
     *            set to true to generate test cases also for protected methods.
     * @param includePrivate
     *            set to true to generate test cases also for private methods.
     * @param includeNative
     *            set to true to generate test cases also for methods inherited
     *            from <code>java.lang.Object</code>.
     * @return a test suite for the framework targeted by the implementor.
     */
    public String generateFullTestSuite(final String source,
            final ICodeCoverageParser coverage, final boolean includeProtected,
            final boolean includePrivate, final boolean includeNative)
            throws TestGeneratorException {

        return null;
    }

    /**
     * Generates a test suite covering a single method in a Java source file.
     * 
     * @param source
     *            path to the Java source file
     * @param methods
     *            the methods to generate the test cases for.
     * @param coverage
     *            code coverage critera to be satisfied by the generated test
     *            cases. May be <code>null</code>, in which case a default
     *            statement coverage is used.
     * @return a test suite for the framework targeted by the implementor.
     */
    public List<String> generatePartialTestSuite(final File source,
            final ICodeCoverageParser coverage,
            final IFrameworkConverter frameworkConverter,
            final String... methods) throws TestGeneratorException {

        Benchmark.startBenchmarking("5. Generate test suite (total time)");

        try {

            /*
             * Create abstract test suites for the selected methods.
             */
            final List<TestSuite> testSuites = coreInterface.createTestSuites(
                    source, coverage, methods);

            /*
             * Convert the abstract test suites to the desired final format.
             */
            Benchmark.startBenchmarking("4. Write to JUnit");
            final List<String> convertedTestSuites = new LinkedList<String>();
            for (final TestSuite testSuite : testSuites) {

                final String convertedTestSuite = frameworkConverter.convert(testSuite);

                convertedTestSuites.add(convertedTestSuite);
            }
            Benchmark.finishBenchmarking("4. Write to JUnit");

            Benchmark.finishBenchmarking("5. Generate test suite (total time)");
            return convertedTestSuites;

        } catch (final CoreException e) {
            throw new TestGeneratorException(e.getMessage());
        } catch (final FrameworkConverterException e) {
            throw new TestGeneratorException(e.getMessage());
        }
    }

    public List<String> generatePartialTestSuite(final String source,
            final ICodeCoverageParser coverage,
            final IFrameworkConverter frameworkConverter,
            final String... methods) throws TestGeneratorException {

        File file = new File(source);
        if (!file.exists()) {
            throw new TestGeneratorException("No such file or directory: "
                    + source);
        } else {
            return generatePartialTestSuite(file, coverage, frameworkConverter,
                    methods);
        }
    }

    /**
     * Generates a test case for a single {@link IExecutionNode} instance,
     * corresponding to a single statement in a single method.
     * 
     * @param targetNode
     *            the target program node
     * @param services
     *            {@link Services} instance for the execution node
     * @return the entire test suite as a String.
     * @throws TestGeneratorException
     *             in the event that something went wrong.
     */
    public String generateTestCase(final IExecutionNode targetNode,
            final Services services) throws TestGeneratorException {

        return null;
    }
}
