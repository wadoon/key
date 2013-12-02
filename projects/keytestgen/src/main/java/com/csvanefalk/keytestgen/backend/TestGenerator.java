package com.csvanefalk.keytestgen.backend;

import com.csvanefalk.keytestgen.core.CoreException;
import com.csvanefalk.keytestgen.core.CoreInterface;
import com.csvanefalk.keytestgen.core.codecoverage.ICodeCoverageParser;
import com.csvanefalk.keytestgen.core.testsuiteabstraction.TestSuite;
import com.csvanefalk.keytestgen.util.Benchmark;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

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
 * <p/>
 * For any of the options above, the user has the option deciding the level of
 * code coverage to be provided, by supplying an instance of
 * {@link ICodeCoverageParser}. By default. Statement Coverage should be
 * targeted.
 *
 * @author christopher
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
     * Interface to the KeYTestGen2 Core system.
     */
    private final CoreInterface coreInterface = CoreInterface.getInstance();

    /**
     * Generates a test case for a single {@link IExecutionNode} instance,
     * corresponding to a single statement in a single method.
     *
     * @param targetNode the target program node
     * @param services   {@link Services} instance for the execution node
     * @return the entire test suite as a String.
     * @throws TestGeneratorException in the event that something went wrong.
     */
    public ITestSuite generateTestCase(final IExecutionNode targetNode,
                                       final Services services) throws TestGeneratorException {

        return null;
    }

    /**
     * @param source           path to the Java source file.
     * @param coverage         code coverage critera to be satisfied by the generated test
     *                         cases. May be <code>null</code>, in which case a default
     *                         statement coverage is used. See {@link ICodeCoverageParser}.
     * @param converter        converter to turn the output of KTG into code for a given
     *                         testing framework. See {@link IFrameworkConverter}.
     * @param includePublic    set to true to generate test cases for all public methods.
     * @param includeProtected set to true to generate test cases for all protected methods.
     * @param includePrivate   set to true to generate test cases for all private methods.
     * @param includeNative    set to true to generate test cases also for methods inherited
     *                         from <code>java.lang.Object</code>.
     * @return a test suite for the target class, in the specified test
     *         framework.
     * @throws TestGeneratorException in the event that something went wrong in the process of test
     *                                case generation.
     */
    public List<ITestSuite> generateTestSuite(final String source,
                                              final ICodeCoverageParser coverage,
                                              final IFrameworkConverter converter, final boolean includePublic,
                                              final boolean includeProtected, final boolean includePrivate,
                                              final boolean includeNative) throws TestGeneratorException {

        return generateTestSuite(source, coverage, converter, includePublic,
                includeProtected, includePrivate, includeNative,
                new LinkedList<String>());
    }

    /**
     * Generate a set of test suites for a selection of methods in a Java source
     * file. The test suites will will be in accord with the code coverage
     * criteria specified.
     *
     * @param source           path to the Java source file.
     * @param coverage         code coverage critera to be satisfied by the generated test
     *                         cases. May be <code>null</code>, in which case a default
     *                         statement coverage is used. See {@link ICodeCoverageParser}.
     * @param converter        converter to turn the output of KTG into code for a given
     *                         testing framework. See {@link IFrameworkConverter}.
     * @param includePublic    set to true to generate test cases for all public methods.
     * @param includeProtected set to true to generate test cases for all protected methods.
     * @param includePrivate   set to true to generate test cases for all private methods.
     * @param includeNative    set to true to generate test cases also for methods inherited
     *                         from <code>java.lang.Object</code>.
     * @return a test suite for the target class, in the specified test
     *         framework.
     * @throws TestGeneratorException in the event that something went wrong in the process of test
     *                                case generation.
     */
    public List<ITestSuite> generateTestSuite(final String source,
                                              final ICodeCoverageParser coverage,
                                              final IFrameworkConverter converter, final boolean includePublic,
                                              final boolean includeProtected, final boolean includePrivate,
                                              final boolean includeNative, final List<String> methods)
            throws TestGeneratorException {

        Benchmark.startBenchmarking("5. Generate test suite (total time)");

        try {

            final File file = new File(source);

            if (!file.exists()) {
                throw new TestGeneratorException("No such file or directory: "
                        + source);
            }

            /*
             * Create abstract test suites for the selected methods.
             */
            final List<TestSuite> testSuites = coreInterface.createTestSuites(
                    file, coverage, includePublic, includeProtected,
                    includePrivate, includeNative, methods);

            /*
             * Convert the abstract test suites to the desired final format.
             */
            Benchmark.startBenchmarking("4. Write to JUnit");
            final List<ITestSuite> convertedTestSuites = new LinkedList<ITestSuite>();
            for (final TestSuite testSuite : testSuites) {

                final ITestSuite convertedTestSuite = converter.convert(testSuite);

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

    /**
     * Generate a set of test suites for a selection of methods in a Java source
     * file. The test suites will will be in accord with the code coverage
     * criteria specified.
     *
     * @param source    path to the Java source file.
     * @param coverage  code coverage critera to be satisfied by the generated test
     *                  cases. May be <code>null</code>, in which case a default
     *                  statement coverage is used. See {@link ICodeCoverageParser}.
     * @param converter converter to turn the output of KTG into code for a given
     *                  testing framework. See {@link IFrameworkConverter}.
     * @return a test suite for the target class, in the specified test
     *         framework.
     * @throws TestGeneratorException in the event that something went wrong in the process of test
     *                                case generation.
     */
    public List<ITestSuite> generateTestSuite(final String source,
                                              final ICodeCoverageParser coverage,
                                              final IFrameworkConverter converter, final List<String> methods)
            throws TestGeneratorException {

        return generateTestSuite(source, coverage, converter, false, false,
                false, false, methods);
    }

    public static void __DEBUG_DISPOSE() {
        instance = null;
        CoreInterface.__DEBUG_DISPOSE();
    }
}
