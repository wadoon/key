package se.gu.svanefalk.testgeneration.backend;

import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;

/**
 * Implementors of this interface represent KeYTestGen2 backend modules, i.e.
 * they represent test case generators for a specific test framework, making use
 * of the KeYTestGen2 runtime.
 * 
 * The API supports the following basic modes of operation:
 * <ul>
 * Generate a test suite only for a subset case methods in a class.</li>
 * <li>
 * Generate a test suite for all methods in a class, with the option of
 * including protected, private and methods inherited from
 * <code>java.lang.Object</code>.</li>
 * </ul>
 * 
 * For any of the option above, the user has the option deciding the level of
 * code coverage to be provided, by supplying an instance of
 * {@link ICodeCoverageParser}. By default. Statement Coverage should be
 * targeted.
 * 
 * @author christopher
 * 
 */
public interface ITestCaseGenerator {

    /**
     * Generates a set of JUnit test cases for a subset of methods in a Java
     * source file.
     * 
     * @param source
     *            path to the Java source file.
     * @param coverage
     *            code coverage critera to be satisfied by the generated test
     *            cases. May be <code>nulll</code>, in which case a default
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
            throws TestGeneratorException;

    /**
     * Generates a test suite covering a subset of methods in a Java source
     * file.
     * 
     * @param source
     *            path to the Java source file
     * @param methods
     *            the methods to generate the test cases for.
     * @param coverage
     *            code coverage critera to be satisfied by the generated test
     *            cases. May be <code>nulll</code>, in which case a default
     *            statement coverage is used.
     * @return a test suite for the framework targeted by the implementor.
     */
    public String generatePartialTestSuite(final String source,
            final ICodeCoverageParser coverage, final String... methods)
            throws TestGeneratorException;
}