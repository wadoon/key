package de.tud.cs.se.ds.psec.compiler;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Paths;

import org.junit.Test;
import org.key_project.util.java.IOUtil;

import de.tud.cs.se.ds.psec.parser.exceptions.TranslationTacletInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
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
    public void testSimpleArithmeticAndIf() throws TranslationTacletInputException,
            ProblemLoaderException, IOException {

        Compiler compiler = new Compiler(
                new File(functionalTestsDir, "simple/ifAndArith/SimpleArithmeticAndIf.java"),
                TMP_OUT_DIR, true, true, false);

        compiler.compile();

        File outputClassFile = new File(TMP_OUT_DIR,
                "de/tud/test/simple/arith/SimpleArithmeticAndIf.class");

        assertTrue("Class file was not written to expected destination",
                outputClassFile.exists());

        try {
            URL url = Paths.get(TMP_OUT_DIR).toFile().toURI().toURL();
            URL[] urls = new URL[] { url };

            URLClassLoader cl = new URLClassLoader(urls);
            Class<?> cls = cl.loadClass("de.tud.test.simple.arith.SimpleArithmeticAndIf");
            cl.close();

            assertNotNull("Compiled class could not be loaded", cls);

            Method method = cls.getMethod("test", int.class, boolean.class);

            //@formatter:off
            @SuppressWarnings("unchecked")
            Triple<Integer, Boolean, Integer>[] testData = new Triple[] {
                new Triple<>(10, true, 5),
                new Triple<>(10, false, 5),
                new Triple<>(4, true, 42),
                new Triple<>(4, false, 42)
            };
            //@formatter:on

            for (Triple<Integer, Boolean, Integer> triple : testData) {
                assertEquals((int) triple.third,
                        (int) method.invoke(null, triple.first, triple.second));
            }
        }
        catch (MalformedURLException | NoSuchMethodException | SecurityException
                | IllegalArgumentException | ClassNotFoundException
                | IllegalAccessException | InvocationTargetException e) {
            e.printStackTrace();
            fail(e.getMessage());
        }
    }

    @Test
    public void testSimpleWhile() throws TranslationTacletInputException,
            ProblemLoaderException, IOException {

        Compiler compiler = new Compiler(
                new File(functionalTestsDir, "simple/loops/whileLoops/SimpleWhile.java"),
                TMP_OUT_DIR, true, true, false);

        compiler.compile();

        File outputClassFile = new File(TMP_OUT_DIR,
                "de/tud/test/simple/loops/whileLoops/SimpleWhile.class");

        assertTrue("Class file was not written to expected destination",
                outputClassFile.exists());

        try {
            URL url = Paths.get(TMP_OUT_DIR).toFile().toURI().toURL();
            URL[] urls = new URL[] { url };

            URLClassLoader cl = new URLClassLoader(urls);
            Class<?> cls = cl.loadClass("de.tud.test.simple.loops.whileLoops.SimpleWhile");
            cl.close();

            assertNotNull("Compiled class could not be loaded", cls);

            Method method = cls.getMethod("test", int.class);

            //@formatter:off
            @SuppressWarnings("unchecked")
            Pair<Integer, Integer>[] testData = new Pair[] {
                new Pair<>(10, 0),
                new Pair<>(100, 0),
                new Pair<>(42, 0),
                new Pair<>(-1, -1)
            };
            //@formatter:on

            for (Pair<Integer, Integer> triple : testData) {
                assertEquals((int) triple.second,
                        (int) method.invoke(null, triple.first));
            }
        }
        catch (MalformedURLException | NoSuchMethodException | SecurityException
                | IllegalArgumentException | ClassNotFoundException
                | IllegalAccessException | InvocationTargetException e) {
            e.printStackTrace();
            fail(e.getMessage());
        }
    }

    @Test
    public void testSimpleFor() throws TranslationTacletInputException,
            ProblemLoaderException, IOException {

        Compiler compiler = new Compiler(
                new File(functionalTestsDir, "simple/loops/forLoops/SimpleFor.java"),
                TMP_OUT_DIR, true, true, false);

        compiler.compile();

        File outputClassFile = new File(TMP_OUT_DIR,
                "de/tud/test/simple/loops/forLoops/SimpleFor.class");

        assertTrue("Class file was not written to expected destination",
                outputClassFile.exists());

        try {
            URL url = Paths.get(TMP_OUT_DIR).toFile().toURI().toURL();
            URL[] urls = new URL[] { url };

            URLClassLoader cl = new URLClassLoader(urls);
            Class<?> cls = cl.loadClass("de.tud.test.simple.loops.forLoops.SimpleFor");
            cl.close();

            assertNotNull("Compiled class could not be loaded", cls);

            Method method = cls.getMethod("test", int.class);

            //@formatter:off
            @SuppressWarnings("unchecked")
            Pair<Integer, Integer>[] testData = new Pair[] {
                new Pair<>(10, 20),
                new Pair<>(100, 110),
                new Pair<>(42, 52),
                new Pair<>(-1, 9)
            };
            //@formatter:on

            for (Pair<Integer, Integer> triple : testData) {
                assertEquals((int) triple.second,
                        (int) method.invoke(null, triple.first));
            }
        }
        catch (MalformedURLException | NoSuchMethodException | SecurityException
                | IllegalArgumentException | ClassNotFoundException
                | IllegalAccessException | InvocationTargetException e) {
            e.printStackTrace();
            fail(e.getMessage());
        }
    }

}
