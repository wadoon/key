package de.uka.ilkd.key.testgeneration.backend;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.codecoverage.ICodeCoverageParser;

/**
 * Represents the core interface for KeYTestGen2. Implementations can be
 * provided based on which framework (if any) they target.
 * 
 * The API supports the following basic modes of operation:
 * <ul>
 * <li>
 * Generate a test case only for a single {@link IExecutionNode} instance
 * (provided for compatibility with the Symbolic Debugger, may not be relevant
 * to ordinary users).</li>
 * <li>
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
            final Services services) throws TestGeneratorException;

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
     * @return The JUnit test class, containing all test cases for the method
     */
    public String generatePartialTestSuite(final String source,
            final ICodeCoverageParser coverage, final String... methods)
            throws TestGeneratorException;

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
     * @return A String representing the test suite, containing all test cases
     *         for all methods in the file.
     */
    public String generateFullTestSuite(final String source,
            final ICodeCoverageParser coverage, final boolean includeProtected,
            final boolean includePrivate, final boolean includeNative)
            throws TestGeneratorException;
}