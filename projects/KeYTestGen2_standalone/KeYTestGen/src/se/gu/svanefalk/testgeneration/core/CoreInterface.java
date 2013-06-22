package se.gu.svanefalk.testgeneration.core;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import se.gu.svanefalk.testgeneration.backend.IFrameworkConverter;
import se.gu.svanefalk.testgeneration.backend.TestGenerator;
import se.gu.svanefalk.testgeneration.backend.TestGeneratorException;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClass;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClassFactory;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaMethod;
import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;
import se.gu.svanefalk.testgeneration.core.codecoverage.implementation.StatementCoverageParser;
import se.gu.svanefalk.testgeneration.core.concurrency.capsules.CapsuleController;
import se.gu.svanefalk.testgeneration.core.concurrency.capsules.CapsuleExecutor;
import se.gu.svanefalk.testgeneration.core.concurrency.capsules.ICapsule;
import se.gu.svanefalk.testgeneration.core.concurrency.capsules.MethodCapsule;
import se.gu.svanefalk.testgeneration.core.concurrency.monitor.CaughtException;
import se.gu.svanefalk.testgeneration.core.concurrency.monitor.ICapsuleMonitor;
import se.gu.svanefalk.testgeneration.core.concurrency.monitor.IMonitorEvent;
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
public class CoreInterface implements ICapsuleMonitor {

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

    private boolean isNativeMethod(KeYJavaMethod method) {

        return nativeMethods.contains(method.getName());
    }

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
     * Generate a set of test suites for a selection of methods in a Java source
     * file. The test suites will will be in accord with the code coverage
     * criteria specified.
     * 
     * @param source
     *            path to the Java source file.
     * @param coverage
     *            code coverage critera to be satisfied by the generated test
     *            cases. May be <code>null</code>, in which case a default
     *            statement coverage is used. See {@link ICodeCoverageParser}.
     * @param converter
     *            converter to turn the output of KTG into code for a given
     *            testing framework. See {@link IFrameworkConverter}.
     * @return a test suite for the target class, in the specified test
     *         framework.
     * @throws TestGeneratorException
     *             in the event that something went wrong in the process of test
     *             case generation.
     */
    public List<TestSuite> createTestSuites(final File source,
            final ICodeCoverageParser codeCoverageParser,
            final boolean includePublic, final boolean includeProtected,
            final boolean includePrivate, final boolean includeNative,
            final List<String> methods) throws CoreException {

        /*
         * Get the abstract representation of the class.
         */
        final KeYJavaClass targetClass = extractKeYJavaClass(source);

        List<String> selectedMethods = filterMethods(targetClass,
                includePublic, includeProtected, includePrivate, includeNative);

        return createTestSuites(targetClass, codeCoverageParser,
                selectedMethods);
    }

    private List<String> filterMethods(KeYJavaClass targetClass,
            boolean includePublic, boolean includeProtected,
            boolean includePrivate, boolean includeNative) {

        List<String> filteredMethod = new LinkedList<>();
        for (String methodIdentifier : targetClass.getMethods()) {

            KeYJavaMethod method = targetClass.getMethod(methodIdentifier);

            /*
             * Treat native methods first and continue if they are found, since
             * some of them are protected and hence might be included even
             * though they should not be.
             */
            if (isNativeMethod(method)) {
                if (includeNative) {
                    filteredMethod.add(methodIdentifier);
                }
            }

            else if (includePublic && method.isPublic()) {
                filteredMethod.add(methodIdentifier);
            }

            else if (includeProtected && method.isProtected()) {

                filteredMethod.add(methodIdentifier);
            }

            else if (includePrivate && method.isPrivate()) {
                filteredMethod.add(methodIdentifier);
            }
        }

        return filteredMethod;
    }

    /**
     * Main method for invoking the core system itself.
     * 
     * @param targetClass
     * @param codeCoverageParser
     * @param methods
     * @return
     * @throws CoreException
     */
    private List<TestSuite> createTestSuites(final KeYJavaClass targetClass,
            final ICodeCoverageParser codeCoverageParser,
            final List<String> methods) throws CoreException {

        /*
         * The result set of abstract test suites.
         */
        final List<TestSuite> testSuites = new LinkedList<TestSuite>();

        /*
         * Create a MethodCapsule for method selected for test case generation.
         * These capsules will then carry out the test generation process
         * concurrently.
         */
        final CapsuleController<MethodCapsule> controller = new CapsuleController<>();
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
            final MethodCapsule testGenerationCapsule = new MethodCapsule(
                    codeCoverageParser, targetMethod);

            controller.addChild(testGenerationCapsule);
            testGenerationCapsule.addMonitor(this);
        }

        /*
         * Finally, dispatch the capsules and wait for them to finish.
         */
        controller.executeAndWait();

        /*
         * Collect and return the results of the capsules.
         */
        for (final MethodCapsule capsule : controller.getCapsules()) {
            testSuites.add(capsule.getResult());
            // Benchmark.startBenchmarking("Create abstract test cases");
        }

        /*
         * Collect and return the results of the capsules.
         */
        for (final MethodCapsule capsule : controller.getCapsules()) {
            testSuites.add(capsule.getResult());
            // Benchmark.startBenchmarking("Create abstract test cases");
        }

        return testSuites;
    }

    /**
     * Notify this monitor that an event took place in a monitored Capsule.
     */
    @Override
    public void doNotify(final ICapsule source, final IMonitorEvent event) {

        /*
         * The signalling capsule caught an exception
         */
        if (event instanceof CaughtException) {

            /*
             * Notify monitors about the exceptioon
             */
            final CaughtException caughtException = (CaughtException) event;
            caughtException.getPayload();

            /*
             * Terminate all children
             */
            source.getController().stopChildren();
        }
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

            final KeYJavaClass keYJavaClass = keYJavaClassFactory.createKeYJavaClass(source);

            Benchmark.finishBenchmarking("1. [KeY] setting up class and method abstractions");

            return keYJavaClass;

        } catch (final KeYInterfaceException e) {
            throw new CoreException(e.getMessage());
        } catch (final IOException e) {
            throw new CoreException(e.getMessage());
        }
    }
}