package com.csvanefalk.keytestgen.core.concurrency.capsules;

import com.csvanefalk.keytestgen.backend.TestGeneratorException;
import com.csvanefalk.keytestgen.core.CoreException;
import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaClass;
import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaClassFactory;
import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaMethod;
import com.csvanefalk.keytestgen.core.codecoverage.ICodeCoverageParser;
import com.csvanefalk.keytestgen.core.concurrency.monitor.CaughtException;
import com.csvanefalk.keytestgen.core.concurrency.monitor.ICapsuleMonitor;
import com.csvanefalk.keytestgen.core.concurrency.monitor.IMonitorEvent;
import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.core.testsuiteabstraction.TestSuite;
import com.csvanefalk.keytestgen.util.Benchmark;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

public class ClassCapsule extends AbstractCapsule implements ICapsuleMonitor {

    private final ICodeCoverageParser codeCoverageParser;
    /**
     * Used in order to generate instances of {@link KeYJavaClass} for a given
     * source file
     */
    protected final KeYJavaClassFactory keYJavaClassFactory = KeYJavaClassFactory.getInstance();
    private final List<String> methods;
    private final File source;

    private List<TestSuite> testSuites = null;

    public ClassCapsule(final ICodeCoverageParser codeCoverageParser, final List<String> methods, final File source) {
        super();
        this.codeCoverageParser = codeCoverageParser;
        this.methods = methods;
        this.source = source;
    }

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
            final Throwable payload = caughtException.getPayload();
            setThrownException(payload);
            notifyMonitors(event);

            /*
             * Terminate all children
             */
            source.getController().stopChildren();
        }
    }

    @Override
    public void doWork() {

        try {

            /*
             * Get the abstract representation of the class.
             */
            final KeYJavaClass targetClass = extractKeYJavaClass(source);

            /*
             * The result set of abstract test suites.
             */
            final List<TestSuite> testSuites = new LinkedList<TestSuite>();

            /*
             * Create a MethodCapsule for method selected for test case
             * generation. These capsules will then carry out the test
             * generation process concurrently.
             */
            final CapsuleController<MethodCapsule> controller = new CapsuleController<MethodCapsule>();
            for (final String method : methods) {

                /*
                 * Abort if the method cannot be found
                 */
                final KeYJavaMethod targetMethod = targetClass.getMethod(method);
                if (targetMethod == null) {

                    throw new CoreException("No such method: " + method + " in class " + targetClass.getName());
                }

                /*
                 * Setup and ready the capsule
                 */
                final MethodCapsule testGenerationCapsule = new MethodCapsule(codeCoverageParser, targetMethod);

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

            this.testSuites = testSuites;

        } catch (final Exception e) {
            setThrownException(e);
            notifyMonitors(new CaughtException(e));
            return;
        }

        setSucceeded();
    }

    /**
     * This helper method will construct a {@link KeYJavaClass} instance for the
     * public class in a given Java source file.
     *
     * @param source path to the source file
     * @return a {@link KeYJavaClass} instance corresponding to the public class
     * in the source file
     * @throws TestGeneratorException in the event that there is a failure in the KeYInterface, or
     *                                if there is a problem finding or reading the source file.
     */
    private KeYJavaClass extractKeYJavaClass(final File source) throws CoreException {

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

    public List<TestSuite> getResult() {
        return testSuites;
    }

}
