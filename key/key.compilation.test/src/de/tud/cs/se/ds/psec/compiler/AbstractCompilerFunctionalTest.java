package de.tud.cs.se.ds.psec.compiler;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;

import org.key_project.util.java.IOUtil;

import de.tud.cs.se.ds.psec.parser.exceptions.TranslationTacletInputException;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import junit.framework.TestCase;

/**
 * Abstract template for functional compiler tests.
 *
 * @author Dominic Scheurer
 */
public abstract class AbstractCompilerFunctionalTest extends TestCase {
    private static final String FUNCTIONAL_TESTS_RELATIVE_DIR = "/resources/testcase/functional/";
    private static final String TMP_OUT_DIR = "./testTmp/";

    private String functionalTestsDir;

    @Override
    protected void setUp() throws Exception {
        Files.createDirectories(Paths.get(TMP_OUT_DIR));

        File projectRoot = IOUtil
                .getProjectRoot(SimpleCompilerFunctionalTests.class);
        functionalTestsDir = projectRoot + FUNCTIONAL_TESTS_RELATIVE_DIR;
    }

    @Override
    protected void tearDown() throws Exception {
         Utilities.recursivelyRemoveFiles(Paths.get(TMP_OUT_DIR));
    }

    /**
     * Compiles, loads and tests a static method.
     * 
     * @param testMethodName
     *            The name of the method to test.
     * @param argTypes
     *            An array of {@link Class}es of the arguments for the method to
     *            test.
     * @param testData
     *            The {@link TestData} object.
     * @param <C>
     *            The type for the expected results in the test data.
     */
    protected <C> void compileAndTest(String relPathToJavaFile, String className,
            String testMethodName, Class<?>[] argTypes,
            List<TestData<C>> testData) {

        try {

            Class<?> cls = compile(relPathToJavaFile, className);
            assertNotNull("Compiled class could not be loaded", cls);
            runTests(cls, testMethodName, argTypes, testData);

        } catch (SecurityException | IllegalArgumentException
                | TranslationTacletInputException e) {
            e.printStackTrace();
            fail(e.getMessage());
        }
    }

    /**
     * Compiles, loads and tests a static method.
     * 
     * @param cls
     *            The {@link Class} containing the method to test.
     * @param testMethodName
     *            The name of the method to test.
     * @param argTypes
     *            An array of {@link Class}es of the arguments for the method to
     *            test.
     * @param testData
     *            The {@link TestData} object.
     * @param <C>
     *            The type for the expected results in the test data.
     */
    protected <C> void runTests(Class<?> cls, String testMethodName,
            Class<?>[] argTypes, List<TestData<C>> testData) {

        try {

            Method method = cls.getMethod(testMethodName, argTypes);

            for (TestData<C> testItem : testData) {
                //@formatter:off
                assertEquals(
                        testItem.getExpectedResult(),
                        method.invoke(
                                testItem.getThisObject(),
                                testItem.getArguments()));
                //@formatter:on
            }

        } catch (NoSuchMethodException | SecurityException
                | IllegalArgumentException | IllegalAccessException
                | InvocationTargetException
                | TranslationTacletInputException e) {
            e.printStackTrace();
            fail(e.getMessage());
        }
    }

    /**
     * Compiles the class with name <code>className</code> in the Java file at
     * the path <code>relPathToJavaFile</code>.
     * 
     * @param relPathToJavaFile
     *            The path to the Java file to test, relative to
     *            {@link #FUNCTIONAL_TESTS_RELATIVE_DIR}.
     * @param className
     *            The fully qualified class name of the class to test.
     * @return The compiled {@link Class} file, if compilation was successful;
     *         otherwise, the test will {@link #fail()}.
     */
    protected Class<?> compile(String relPathToJavaFile, String className) {
        try {

            Compiler compiler = new Compiler(
                    new File(functionalTestsDir, relPathToJavaFile),
                    TMP_OUT_DIR, true, true, false);

            compiler.compile();

            File outputClassFile = new File(TMP_OUT_DIR,
                    className.replace('.', '/') + ".class");

            assertTrue("Class file was not written to expected destination",
                    outputClassFile.exists());

            URL url = Paths.get(TMP_OUT_DIR).toFile().toURI().toURL();
            URL[] urls = new URL[] { url };

            URLClassLoader cl = new URLClassLoader(urls);
            Class<?> cls = cl.loadClass(className);
            cl.close();

            return cls;

        } catch (TranslationTacletInputException | ProblemLoaderException
                | IOException | ClassNotFoundException e) {
            e.printStackTrace();
            fail(e.getMessage());
            return null;
        }
    }

    /**
     * Encapsulates data for testing a method.
     *
     * @author Dominic Scheurer
     * @param <C>
     *            The type of the expected result.
     */
    protected static class TestData<C> {
        private C expectedResult;
        private Object thisObject;
        private Object[] arguments;

        /**
         * @param expectedResult
         *            The expected result for the test.
         * @param thisObject
         *            The "this" object for executing a method. May be null if
         *            the method under test is static.
         * @param arguments
         *            The arguments for the test.
         */
        public TestData(C expectedResult, Object thisObject,
                Object... arguments) {
            this.expectedResult = expectedResult;
            this.thisObject = thisObject;
            this.arguments = arguments;
        }

        public C getExpectedResult() {
            return expectedResult;
        }

        public Object getThisObject() {
            return thisObject;
        }

        public Object[] getArguments() {
            return arguments;
        }
    }

}
