package de.tud.cs.se.ds.psec.compiler;

import static org.junit.Assert.assertNotEquals;

import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;

import de.tud.cs.se.ds.psec.parser.exceptions.TranslationTacletInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * Functional test cases for the compiler (i.e., Java code is compiled,
 * executed, and tested for correctness).
 *
 * @author Dominic Scheurer
 */
public class SimpleCompilerFunctionalTests extends AbstractCompilerFunctionalTest {

    public SimpleCompilerFunctionalTests() {
        super(false);
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

            // Test "equals" method with SimpleObjects argument
            List<TestData<Boolean>> testDataEquals = Arrays.asList(
                    new TestData<Boolean>(true, o1, o1),
                    new TestData<Boolean>(true, o1, o2),
                    new TestData<Boolean>(false, o1, o3));

            runTests(simpleObjects, "equals", new Class<?>[] { simpleObjects },
                    testDataEquals);
            
            // Test "equals" method with Object argument
            List<TestData<Boolean>> testDataEqualsObj = Arrays.asList(
                    new TestData<Boolean>(true, o1, o1),
                    new TestData<Boolean>(true, o1, o2),
                    new TestData<Boolean>(false, o1, o3),
                    new TestData<Boolean>(false, o1, new Object()),
                    new TestData<Boolean>(true, o1, (Object) o2));

            runTests(simpleObjects, "equals", new Class<?>[] { Object.class },
                    testDataEqualsObj);

        } catch (NoSuchMethodException | SecurityException
                | InstantiationException | IllegalAccessException
                | IllegalArgumentException | InvocationTargetException
                | NoSuchFieldException e) {
            e.printStackTrace();
            fail(e.getMessage());
        }

    }

}
