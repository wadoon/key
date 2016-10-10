package de.tud.cs.se.ds.psec.compiler;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
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
    public void testEqualsAndSetMethods() {

        Class<?> methodCalls = compile("methods/MethodCalls.java",
                "de.tud.test.methods.MethodCalls");

        try {

            Constructor<?> ctor = methodCalls.getConstructor(int.class);

            Object o1 = ctor.newInstance(1);
            Object o2 = ctor.newInstance(1);
            Object o3 = ctor.newInstance(2);

            // Test "equals" method with SimpleObjects argument
            List<TestData<Boolean>> testDataEquals = Arrays.asList(
                    new TestData<Boolean>(true, o1, o1),
                    new TestData<Boolean>(true, o1, o2),
                    new TestData<Boolean>(false, o1, o3));

            runTests(methodCalls, "equals", new Class<?>[] { methodCalls },
                    testDataEquals);

            // Test "equals" method with Object argument
            List<TestData<Boolean>> testDataEqualsObj = Arrays.asList(
                    new TestData<Boolean>(true, o1, o1),
                    new TestData<Boolean>(true, o1, o2),
                    new TestData<Boolean>(false, o1, o3),
                    new TestData<Boolean>(false, o1, new Object()),
                    new TestData<Boolean>(true, o1, (Object) o2));

            runTests(methodCalls, "equals", new Class<?>[] { Object.class },
                    testDataEqualsObj);

            runTests(methodCalls, "equals2", new Class<?>[] { Object.class },
                    testDataEqualsObj);

            // Test "set(int)" method
            callMethod(methodCalls, "set", o1, new Class<?>[] { int.class }, 2);

            List<TestData<Boolean>> testDataEqualsObjAfterSet = Arrays.asList(
                    new TestData<Boolean>(true, o1, o1),
                    new TestData<Boolean>(false, o1, o2),
                    new TestData<Boolean>(true, o1, o3),
                    new TestData<Boolean>(false, o1, new Object()),
                    new TestData<Boolean>(false, o1, (Object) o2));

            runTests(methodCalls, "equals", new Class<?>[] { Object.class },
                    testDataEqualsObjAfterSet);

            // Test "set(MethodCalls, int)" method
            // We set the field back to its previous value, so the previous
            // tests should pass through
            callMethod(methodCalls, "set", null,
                    new Class<?>[] { methodCalls, int.class }, o1, 1);

            runTests(methodCalls, "equals", new Class<?>[] { Object.class },
                    testDataEqualsObj);

            runTests(methodCalls, "equals2", new Class<?>[] { Object.class },
                    testDataEqualsObj);

            // Test "set2(int)" method
            // We set the field to 2 again, so the test before the previous
            // one should pass through again
            callMethod(methodCalls, "set2", o1,
                    new Class<?>[] { int.class }, 2);

            runTests(methodCalls, "equals", new Class<?>[] { Object.class },
                    testDataEqualsObjAfterSet);

        } catch (NoSuchMethodException | SecurityException
                | InstantiationException | IllegalAccessException
                | IllegalArgumentException | InvocationTargetException e) {
            e.printStackTrace();
            fail(e.getMessage());
        }

    }

}
