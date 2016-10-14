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

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
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
    private static final Logger logger = LogManager.getFormatterLogger();
    private static final String FUNCTIONAL_TESTS_RELATIVE_DIR = "/resources/testcase/functional/";
    private static final String TMP_OUT_DIR = "./testTmp/";

    private String functionalTestsDir;
    private boolean deleteTmpFiles;

    public AbstractCompilerFunctionalTest(boolean deleteTmpFiles) {
        this.deleteTmpFiles = deleteTmpFiles;
    }

    @Override
    protected void setUp() throws Exception {
        Files.createDirectories(Paths.get(TMP_OUT_DIR));

        File projectRoot = IOUtil
                .getProjectRoot(SimpleCompilerFunctionalTests.class);
        functionalTestsDir = projectRoot + FUNCTIONAL_TESTS_RELATIVE_DIR;
    }

    @Override
    protected void tearDown() throws Exception {
        if (deleteTmpFiles) {
            Utilities.recursivelyRemoveFiles(Paths.get(TMP_OUT_DIR));
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
    protected <C> void compileAndTest(String relPathToJavaFile,
            String className, String testMethodName, Class<?>[] argTypes,
            List<TestData<C>> testData) {

        try {

            Class<?> cls = compileAndLoad(relPathToJavaFile, className);
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
    protected static <C> void runTests(Class<?> cls, String testMethodName,
            Class<?>[] argTypes, List<TestData<C>> testData) {

        try {

            Method method = findMethod(cls, testMethodName, argTypes);

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
     * Calls a method via reflection and returns the result; if the called
     * method is void, the result will be null. Any exception will cause the
     * calling test case to fail.
     * 
     * @param cls
     *            The {@link Class} containing the method.
     * @param testMethodName
     *            The name of the {@link Method}.
     * @param obj
     *            The object to call the {@link Method} on. May be null for
     *            static {@link Method}s.
     * @param argTypes
     *            The array of argument types.
     * @param args
     *            The actual arguments for the method call.
     * @return The result of the call, or null if the method is void or the call
     *         induces an {@link Exception}.
     * 
     * @see Class#getMethod(String, Class...)
     * @see Method#invoke(Object, Object...)
     */
    protected static Object callMethod(Class<?> cls, String testMethodName,
            Object obj, Class<?>[] argTypes, Object... args) {
        try {

            Method method = findMethod(cls, testMethodName, argTypes);
            return method.invoke(obj, args);

        } catch (SecurityException | IllegalAccessException
                | IllegalArgumentException | InvocationTargetException
                | NoSuchMethodException e) {
            e.printStackTrace();
            fail(e.getMessage());
            return null;
        }
    }

    /**
     * Finds a method with the given name and parameters; the method may also be
     * non-public, which distinguishes this procedure from
     * {@link Class#getMethod(String, Class...)} that recursively looks up
     * <strong>public</strong> methods, and from
     * {@link Class#getDeclaredMethod(String, Class...)} which works for all
     * methods actually declared in the given class, but won't find even public
     * super methods.
     * <p>
     * If the given method is not accessible, this is changed, and a log entry
     * is documenting that change.
     * 
     * @param cls
     *            The {@link Class} for which to find a {@link Method}.
     * @param testMethodName
     *            The name for the {@link Method} to find.
     * @param argTypes
     *            The argument types for the {@link Method} to find.
     * @return A given {@link Method} of matching signature in either the given
     *         {@link Class} or a super class, or throws a
     *         {@link NoSuchMethodException}.
     * @throws NoSuchMethodException
     *             If there is no matching method, neither in the given
     *             {@link Class} nor in any super class.
     */
    private static Method findMethod(Class<?> cls, String testMethodName,
            Class<?>[] argTypes) throws NoSuchMethodException {
        while (cls != null) {
            try {
                Method method = cls.getDeclaredMethod(testMethodName, argTypes);

                if (!method.isAccessible()) {
                    logger.warn(
                            "Method %s#%s was not accessible, enforcing accessibility",
                            method.getDeclaringClass().getName(),
                            method.getName());
                    method.setAccessible(true);
                }

                return method;
            } catch (NoSuchMethodException e) {
                cls = cls.getSuperclass();
                continue;
            }
        }

        throw new NoSuchMethodException();
    }

    /**
     * Compiles the Java file at the path
     * <code>{@link #FUNCTIONAL_TESTS_RELATIVE_DIR}/relPathToJavaFile</code> and
     * loads the class with name <code>className</code>.
     * 
     * @param relPathToJavaFile
     *            The path to the Java file to test, relative to
     *            {@link #FUNCTIONAL_TESTS_RELATIVE_DIR}.
     * @param className
     *            The fully qualified class name of the class to test.
     * @return The compiled {@link Class}, if compilation was successful;
     *         otherwise, the test will {@link #fail()}.
     */
    protected Class<?> compileAndLoad(String relPathToJavaFile,
            String className) {
        try {

            compile(relPathToJavaFile);
            return loadClass(className);

        } catch (TranslationTacletInputException e) {
            e.printStackTrace();
            fail(e.getMessage());
            return null;
        }
    }

    /**
     * Compiles the Java file at the path
     * <code>{@link #FUNCTIONAL_TESTS_RELATIVE_DIR}/relPathToJavaFile</code> and
     * loads the classes with names <code>classNames</code>.
     * 
     * @param relPathToJavaFile
     *            The path to the Java file to test, relative to
     *            {@link #FUNCTIONAL_TESTS_RELATIVE_DIR}.
     * @param classNames
     *            The fully qualified class names of the class to test.
     * @return The compiled {@link Class}es, if compilation was successful;
     *         otherwise, the test will {@link #fail()}.
     */
    protected Class<?>[] compileAndLoad(String relPathToJavaFile,
            String... classNames) {
        if (classNames == null) {
            String msg = "null array of class names given";
            logger.error(msg);
            throw new NullPointerException(msg);
        }

        try {

            compile(relPathToJavaFile);
            return loadClasses(classNames);

        } catch (TranslationTacletInputException e) {
            e.printStackTrace();
            fail(e.getMessage());
            return null;
        }
    }

    /**
     * Compiles the Java file at the path <code>relPathToJavaFile</code>.
     * 
     * @param relPathToJavaFile
     *            relPathToJavaFile The path to the Java file to test, relative
     *            to {@link #FUNCTIONAL_TESTS_RELATIVE_DIR}.
     */
    protected void compile(String relPathToJavaFile) {
        try {

            Compiler compiler = new Compiler(
                    new File(functionalTestsDir, relPathToJavaFile),
                    TMP_OUT_DIR, true, true, false);

            compiler.compile();

        } catch (TranslationTacletInputException | ProblemLoaderException
                | IOException e) {
            e.printStackTrace();
            fail(e.getMessage());
        }
    }

    /**
     * Loads the {@link Class} with the given name from the {@link #TMP_OUT_DIR}
     * directory.
     * 
     * @param className
     *            The fully qualified class name of the class to test.
     * @return The loaded {@link Class}.
     */
    protected Class<?> loadClass(String className) {
        return loadClass(className, null);
    }

    /**
     * Loads the {@link Class} with the given name from the {@link #TMP_OUT_DIR}
     * directory.
     * 
     * @param className
     *            The fully qualified class name of the class to test.
     * @param parentClassLoader
     *            The {@link ClassLoader} to use for delegation. May be null.
     * @return The loaded {@link Class}.
     */
    protected Class<?> loadClass(String className,
            ClassLoader parentClassLoader) {
        return loadClasses(new String[] { className }, parentClassLoader)[0];
    }

    /**
     * @see #loadClasses(String[], ClassLoader)
     */
    protected Class<?>[] loadClasses(String... classNames) {
        return loadClasses(classNames, null);
    }

    /**
     * Loads the {@link Class}es with the given names from the
     * {@link #TMP_OUT_DIR} directory.
     * <p>
     * <strong>Use this method instead of
     * {@link #loadClass(String, ClassLoader)} if you want to load multiple
     * dependent classes!</strong> Those need to be loaded with the same
     * {@link ClassLoader}, otherwise you will end up with an
     * {@link IllegalAccessError}.
     * 
     * @param classNames
     *            The fully qualified class names of the classes to test.
     * @param parentClassLoader
     *            The {@link ClassLoader} to use for delegation. May be null.
     * @return The loaded {@link Class}es.
     */
    protected Class<?>[] loadClasses(String[] classNames,
            ClassLoader parentClassLoader) {

        try {
            Class<?>[] result = new Class<?>[classNames.length];

            URL url = Paths.get(TMP_OUT_DIR).toFile().toURI().toURL();
            URL[] urls = new URL[] { url };

            URLClassLoader cl = parentClassLoader == null
                    ? new URLClassLoader(urls)
                    : new URLClassLoader(urls, parentClassLoader);

            for (int i = 0; i < classNames.length; i++) {
                File outputClassFile = new File(TMP_OUT_DIR,
                        classNames[i].replace('.', '/') + ".class");

                assertTrue("Class file was not written to expected destination",
                        outputClassFile.exists());

                result[i] = cl.loadClass(classNames[i]);
            }

            cl.close();

            return result;

        } catch (TranslationTacletInputException | IOException
                | ClassNotFoundException e) {
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
