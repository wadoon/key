package se.gu.svanefalk.testgeneration.core.concurrency.capsules;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import se.gu.svanefalk.testgeneration.backend.TestGeneratorException;
import se.gu.svanefalk.testgeneration.core.CoreException;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClass;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClassFactory;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaMethod;
import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;
import se.gu.svanefalk.testgeneration.core.concurrency.monitor.CaughtException;
import se.gu.svanefalk.testgeneration.core.concurrency.monitor.ICapsuleMonitor;
import se.gu.svanefalk.testgeneration.core.concurrency.monitor.IMonitorEvent;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestSuite;
import se.gu.svanefalk.testgeneration.util.Benchmark;

public class ClassCapsule extends AbstractCapsule implements ICapsuleMonitor {

    /**
     * Used in order to generate instances of {@link KeYJavaClass} for a given
     * source file
     */
    protected final KeYJavaClassFactory keYJavaClassFactory = KeYJavaClassFactory.getInstance();
    private final ICodeCoverageParser codeCoverageParser;
    private final List<String> methods;
    private final File source;

    public ClassCapsule(ICodeCoverageParser codeCoverageParser,
            List<String> methods, File source) {
        super();
        this.codeCoverageParser = codeCoverageParser;
        this.methods = methods;
        this.source = source;
    }

    private List<TestSuite> testSuites = null;

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
            CapsuleController<MethodCapsule> controller = new CapsuleController<>();
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

            this.testSuites = testSuites;

        } catch (Exception e) {
            setThrownException(e);
            notifyMonitors(new CaughtException(e));
            return;
        }

        setSucceeded();
    }

    public List<TestSuite> getResult() {
        return testSuites;
    }

    @Override
    public void doNotify(ICapsule source, IMonitorEvent event) {

        /*
         * The signalling capsule caught an exception
         */
        if (event instanceof CaughtException) {

            /*
             * Notify monitors about the exceptioon
             */
            CaughtException caughtException = (CaughtException) event;
            Throwable payload = caughtException.getPayload();
            setThrownException(payload);
            notifyMonitors(event);

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
