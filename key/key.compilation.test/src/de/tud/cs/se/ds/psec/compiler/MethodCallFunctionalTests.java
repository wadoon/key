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
        super(true);
    }

    @Test
    public void testEqualsAndSetMethods() {

        Class<?> methodCalls = compileAndLoad("methods/MethodCalls.java",
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
            callMethod(methodCalls, "set2", o1, new Class<?>[] { int.class },
                    2);

            runTests(methodCalls, "equals", new Class<?>[] { Object.class },
                    testDataEqualsObjAfterSet);

        } catch (NoSuchMethodException | SecurityException
                | InstantiationException | IllegalAccessException
                | IllegalArgumentException | InvocationTargetException e) {
            e.printStackTrace();
            fail(e.getMessage());
        }

    }

    @Test
    public void testNonPrimitiveMethods() {

        Class<?>[] classes = compileAndLoad(
                "nonprimitive_methods/NonPrimitiveMethods.java",
                "de.tud.test.methods.StringContainer",
                "de.tud.test.methods.NonPrimitiveMethods");

        Class<?> StringContainer = classes[0];
        Class<?> NonPrimitiveMethods = classes[1];

        try {

            Constructor<?> nonPrimitiveMethodsCtor = NonPrimitiveMethods
                    .getConstructor(StringContainer);

            Constructor<?> stringContainerCtor = StringContainer
                    .getConstructor(String.class);

            stringContainerCtor.setAccessible(true);

            Object container1 = stringContainerCtor.newInstance("Monkeys");
            Object container2 = stringContainerCtor.newInstance("Donkeys");

            Object npm1 = nonPrimitiveMethodsCtor.newInstance(container1);
            Object npm1a = nonPrimitiveMethodsCtor.newInstance(container1);
            Object npm2 = nonPrimitiveMethodsCtor.newInstance(container2);

            // Test "equals" of StringContainer
            List<TestData<Boolean>> testDataStringContainerEquals = Arrays
                    .asList(new TestData<Boolean>(true, container1, container1),
                            new TestData<Boolean>(true, container2, container2),
                            new TestData<Boolean>(false, container1,
                                    container2),
                            new TestData<Boolean>(false, container2,
                                    container1));

            runTests(StringContainer, "equals",
                    new Class<?>[] { StringContainer },
                    testDataStringContainerEquals);

            // Test "equals" of NonPrimitiveMethods
            List<TestData<Boolean>> testDataNonPrimitiveMethodsEquals = Arrays
                    .asList(new TestData<Boolean>(true, npm1, npm1),
                            new TestData<Boolean>(true, npm1, npm1a),
                            new TestData<Boolean>(true, npm1a, npm1),
                            new TestData<Boolean>(false, npm1, npm2),
                            new TestData<Boolean>(false, npm1a, npm2),
                            new TestData<Boolean>(false, npm1,
                                    "That's not the expected type!"));

            runTests(NonPrimitiveMethods, "equals",
                    new Class<?>[] { Object.class },
                    testDataNonPrimitiveMethodsEquals);

        } catch (NoSuchMethodException | SecurityException
                | InstantiationException | IllegalAccessException
                | IllegalArgumentException | InvocationTargetException e) {
            e.printStackTrace();
            fail(e.getMessage());
        }

    }

}
