package de.tud.cs.se.ds.psec.compiler;

import static org.junit.Assert.assertNotEquals;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;

/**
 * Functional test cases for the compiler (i.e., Java code is compiled,
 * executed, and tested for correctness).
 *
 * @author Dominic Scheurer
 */
public class MethodCallFunctionalTests extends AbstractCompilerFunctionalTest {

    public MethodCallFunctionalTests() {
        super(false);
    }

    @Test
    public void testObjectConstructionAndMemberAccess() {
        
        Class<?> simpleObjects = compile("methods/MethodCalls.java",
                "de.tud.test.simple.objects.MethodCalls");

        //TODO

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
