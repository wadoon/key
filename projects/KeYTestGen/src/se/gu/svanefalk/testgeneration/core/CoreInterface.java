package se.gu.svanefalk.testgeneration.core;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import se.gu.svanefalk.testgeneration.backend.TestGeneratorException;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClass;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClassFactory;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaMethod;
import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;
import se.gu.svanefalk.testgeneration.core.codecoverage.implementation.StatementCoverageParser;
import se.gu.svanefalk.testgeneration.core.concurrency.CapsuleExecutor;
import se.gu.svanefalk.testgeneration.core.concurrency.TestGenerationCapsule;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestSuite;
import se.gu.svanefalk.testgeneration.util.Benchmark;

/**
 * API singleton for the core package
 * <p>
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
public class CoreInterface {

    private static CoreInterface instance = null;

    public static CoreInterface getInstance() {
        if (CoreInterface.instance == null) {
            CoreInterface.instance = new CoreInterface();
        }
        return CoreInterface.instance;
    }

    private final CapsuleExecutor capsuleExecutor = CapsuleExecutor.getInstance();

    /**
     * Used in order to generate instances of {@link KeYJavaClass} for a given
     * source file
     */
    protected final KeYJavaClassFactory keYJavaClassFactory = KeYJavaClassFactory.getInstance();

    private CoreInterface() {
    }

    /**
     * Creates a set of abstract test suites for a given set of methods belong
     * to a Java class. One test suite per method will be generated.
     * 
     * @param source
     * @param codeCoverageParser
     * @param methods
     * @return
     * @throws CoreException
     */
    public List<TestSuite> createTestSuites(final File source,
            ICodeCoverageParser codeCoverageParser, final String... methods)
            throws CoreException {

        /*
         * If no coverage criteria are specificed, use default.
         */
        if (codeCoverageParser == null) {
            codeCoverageParser = new StatementCoverageParser();
        }

        /*
         * Get the abstract representation of the class.
         */
        final KeYJavaClass targetClass = extractKeYJavaClass(source);

        /*
         * The result set of abstract test suites.
         */
        final List<TestSuite> testSuites = new LinkedList<TestSuite>();

        /*
         * Create a TestGenerationCapsule for method selected for test case
         * generation. These capsules will then carry out the test generation
         * process concurrently.
         */
        final List<TestGenerationCapsule> testGenerationCapsules = new LinkedList<TestGenerationCapsule>();
        for (final String method : methods) {

            /*
             * Abort if the method cannot be found
             */
            final KeYJavaMethod targetMethod = targetClass.getMethod(method);
            if (targetMethod == null) {
                throw new CoreException("No such method: " + method
                        + " in class " + targetClass.getName());
            }

            /*
             * Setup and ready the capsule
             */
            final TestGenerationCapsule testGenerationCapsule = new TestGenerationCapsule(
                    codeCoverageParser, targetMethod);
            testGenerationCapsules.add(testGenerationCapsule);
        }

        /*
         * Finally, dispatch the capsules and wait for them to finish.
         */
        capsuleExecutor.executeCapsulesAndWait(testGenerationCapsules);

        /*
         * Collect and return the results of the capsules.
         */
        for (final TestGenerationCapsule capsule : testGenerationCapsules) {
            testSuites.add(capsule.getResult());
            // Benchmark.startBenchmarking("Create abstract test cases");
        }

        return testSuites;
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
    private KeYJavaClass extractKeYJavaClass(final File source)
            throws CoreException {

        try {

            /*
             * Extract the abstract representations of the targeted Java class
             * and the specific method for which we wish to generate test cases.
             */
            Benchmark.startBenchmarking("1. [KeY] setting up class and method abstractions");

            final KeYJavaClass keYJavaClass = keYJavaClassFactory.createKeYJavaClass(
                    source);

            Benchmark.finishBenchmarking("1. [KeY] setting up class and method abstractions");

            return keYJavaClass;

        } catch (final KeYInterfaceException e) {
            throw new CoreException(e.getMessage());
        } catch (final IOException e) {
            throw new CoreException(e.getMessage());
        }
    }
}