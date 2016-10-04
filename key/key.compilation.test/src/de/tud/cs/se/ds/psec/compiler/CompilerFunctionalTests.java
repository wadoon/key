package de.tud.cs.se.ds.psec.compiler;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;
import org.key_project.util.java.IOUtil;

import de.tud.cs.se.ds.psec.parser.exceptions.TranslationTacletInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import junit.framework.TestCase;

/**
 * Functional test cases for the compiler (i.e., Java code is compiled,
 * executed, and tested for correctness).
 *
 * @author Dominic Scheurer
 */
public class CompilerFunctionalTests extends TestCase {
    private static final String FUNCTIONAL_TESTS_RELATIVE_DIR = "/resources/testcase/functional/";
    private static final String TMP_OUT_DIR = "./testTmp/";

    private String functionalTestsDir;

    @Override
    protected void setUp() throws Exception {
        Files.createDirectories(Paths.get(TMP_OUT_DIR));

        File projectRoot = IOUtil.getProjectRoot(CompilerFunctionalTests.class);
        functionalTestsDir = projectRoot + FUNCTIONAL_TESTS_RELATIVE_DIR;
    }

    @Override
    protected void tearDown() throws Exception {
        // Files.delete(Paths.get(TMP_OUT_DIR));
    }

    @Test
    public void testSimpleArithmeticAndIf() {

        List<TestData<Integer>> testData = Arrays.asList(
                new TestData<Integer>(5, 10, true),
                new TestData<Integer>(5, 10, false),
                new TestData<Integer>(42, 4, true),
                new TestData<Integer>(42, 4, false));

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
                new TestData<Integer>(0, 10), new TestData<Integer>(0, 100),
                new TestData<Integer>(0, 42), new TestData<Integer>(-1, -1));

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
                new TestData<Integer>(16, 10), new TestData<Integer>(106, 100),
                new TestData<Integer>(48, 42), new TestData<Integer>(5, -1));

        //@formatter:off
        compileAndTest(
                "simple/loops/forLoops/SimpleFor.java",
                "de.tud.test.simple.loops.forLoops.SimpleFor",
                "test",
                new Class<?>[] { int.class },
                testData);
        //@formatter:on

    }

    /**
     * Compiles, loads and tests a static method.
     * 
     * @param relPathToJavaFile
     *            The path to the Java file to test, relative to
     *            {@link #FUNCTIONAL_TESTS_RELATIVE_DIR}.
     * @param className
     *            The fully qualified class name of the class to test.
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

            assertNotNull("Compiled class could not be loaded", cls);

            Method method = cls.getMethod(testMethodName, argTypes);

            for (TestData<C> testItem : testData) {
                assertEquals(testItem.getExpectedResult(),
                        method.invoke(null, testItem.getArguments()));
            }
        }
        catch (NoSuchMethodException | SecurityException
                | IllegalArgumentException | ClassNotFoundException
                | IllegalAccessException | InvocationTargetException
                | TranslationTacletInputException | ProblemLoaderException
                | IOException e) {
            e.printStackTrace();
            fail(e.getMessage());
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
        private Object[] arguments;

        public TestData(C expectedResult, Object... arguments) {
            this.expectedResult = expectedResult;
            this.arguments = arguments;
        }

        public C getExpectedResult() {
            return expectedResult;
        }

        public Object[] getArguments() {
            return arguments;
        }
    }

}
