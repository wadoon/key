package de.tud.cs.se.ds.psec.compiler;

import static org.junit.Assert.assertNotEquals;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;
import org.key_project.util.java.IOUtil;

import de.tud.cs.se.ds.psec.parser.exceptions.TranslationTacletInputException;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import junit.framework.TestCase;

/**
 * Functional test cases for the compiler (i.e., Java code is compiled,
 * executed, and tested for correctness).
 *
 * @author Dominic Scheurer
 */
public class SimpleCompilerFunctionalTests extends TestCase {
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

    @Test
    public void testSimpleArithmeticAndIf() {

        List<TestData<Integer>> testData = Arrays.asList(
                new TestData<Integer>(5, null, 10, true),
                new TestData<Integer>(5, null, 10, false),
                new TestData<Integer>(42, null, 4, true),
                new TestData<Integer>(42, null, 4, false));

        //@formatter:off
        compileAndTest(
                "simple/ifAndArith/SimpleArithmeticAndIf.java",
                "de.tud.test.simple.arith.SimpleArithmeticAndIf",
                "test",
                new Class<?>[] { int.class, boolean.class },
                testData);
        //@formatter:on

    }

    @Test
    public void testSimpleWhile() {

        List<TestData<Integer>> testData = Arrays.asList(
                new TestData<Integer>(0, null, 10),
                new TestData<Integer>(0, null, 100),
                new TestData<Integer>(0, null, 42),
                new TestData<Integer>(-1, null, -1));

        //@formatter:off
        compileAndTest(
                "simple/loops/whileLoops/SimpleWhile.java",
                "de.tud.test.simple.loops.whileLoops.SimpleWhile",
                "test",
                new Class<?>[] { int.class },
                testData);
        //@formatter:on

    }

    @Test
    public void testSimpleFor() throws TranslationTacletInputException,
            ProblemLoaderException, IOException {

        List<TestData<Integer>> testData = Arrays.asList(
                new TestData<Integer>(16, null, 10),
                new TestData<Integer>(106, null, 100),
                new TestData<Integer>(48, null, 42),
                new TestData<Integer>(5, null, -1));

        //@formatter:off
        compileAndTest(
                "simple/loops/forLoops/SimpleFor.java",
                "de.tud.test.simple.loops.forLoops.SimpleFor",
                "test",
                new Class<?>[] { int.class },
                testData);
        //@formatter:on

    }

    @Test
    public void testSimpleBoolean() {

        List<TestData<Boolean>> testData = Arrays.asList(
                new TestData<Boolean>(false, null, false, false),
                new TestData<Boolean>(false, null, false, true),
                new TestData<Boolean>(false, null, true, false),
                new TestData<Boolean>(true, null, true, true));

        //@formatter:off
        compileAndTest(
                "simple/boolean/SimpleBoolean.java",
                "de.tud.test.simple.bool.SimpleBoolean",
                "test",
                new Class<?>[] { boolean.class, boolean.class },
                testData);
        //@formatter:on

    }

    @Test
    public void testObjectIdentity() {

        Object o1 = new Object();
        Object o2 = new Object();

        List<TestData<Boolean>> testDataIdentical = Arrays.asList(
                new TestData<Boolean>(true, null, "test", "test"),
                new TestData<Boolean>(true, null, o1, o1),
                new TestData<Boolean>(true, null, o2, o2),
                new TestData<Boolean>(false, null, o1, o2),
                new TestData<Boolean>(false, null, o1, "test"));

        //@formatter:off
        compileAndTest(
                "simple/objects/SimpleObjects.java",
                "de.tud.test.simple.objects.SimpleObjects",
                "identical",
                new Class<?>[] { Object.class, Object.class },
                testDataIdentical);
        //@formatter:on

    }

    @Test
    public void testObjectConstructionAndMemberAccess() {

        Class<?> simpleObjects = compile("simple/objects/SimpleObjects.java",
                "de.tud.test.simple.objects.SimpleObjects");

        try {

            Constructor<?> ctor = simpleObjects.getConstructor(int.class);

            final int paramArg = 1;
            Object o1 = ctor.newInstance(paramArg);

            Field f = o1.getClass().getDeclaredField("i");

            // Assert that the field was correctly compiled as a private one
            assertNotEquals("Field not private as expected", 0,
                    f.getModifiers() & Modifier.PRIVATE);

            // Make the field public to retrieve its value
            f.setAccessible(true);

            assertEquals("Field not initialized as expected", paramArg,
                    f.getInt(o1));

            Object o2 = ctor.newInstance(1);
            Object o3 = ctor.newInstance(2);

            List<TestData<Boolean>> testDataEquals = Arrays.asList(
                    new TestData<Boolean>(true, o1, o1),
                    new TestData<Boolean>(true, o1, o2),
                    new TestData<Boolean>(false, o1, o3));

            runTests(simpleObjects, "equals", new Class<?>[] { simpleObjects },
                    testDataEquals);

        } catch (NoSuchMethodException | SecurityException
                | InstantiationException | IllegalAccessException
                | IllegalArgumentException | InvocationTargetException
                | NoSuchFieldException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

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
    private <C> void compileAndTest(String relPathToJavaFile, String className,
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
    private <C> void runTests(Class<?> cls, String testMethodName,
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
    private Class<?> compile(String relPathToJavaFile, String className) {
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
    private static class TestData<C> {
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
