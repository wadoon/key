package de.tud.cs.se.ds.psec.compiler;

import static org.junit.Assert.*;

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
public class InheritanceFunctionalTest extends AbstractCompilerFunctionalTest {
    private static final boolean DELETE_TMP_FILES = true;

    public InheritanceFunctionalTest() {
        super(DELETE_TMP_FILES);
    }

    @Test
    public void testInheritance() {

        Class<?>[] classes = compileAndLoad("inheritance/Inheritance.java",
                "de.tud.test.inheritance.Inheritance",
                "de.tud.test.inheritance.SuperClass",
                "de.tud.test.inheritance.NatWrapper");

        Class<?> Inheritance = classes[0];
        Class<?> SuperClass = classes[1];
        Class<?> NatWrapper = classes[2];

        try {
            final Object[] emptyObjArray = new Object[0];

            Constructor<?> inheritanceCtor = Inheritance
                    .getConstructor(int.class);

            Object o1 = inheritanceCtor.newInstance(1);
            Object o0 = inheritanceCtor.newInstance(0);
            Object om1 = inheritanceCtor.newInstance(-1);
            Object o17 = inheritanceCtor.newInstance(17);

            // Test "get" and "NatWrapper#toString" methods
            assertEquals("1",
                    callMethod(Inheritance, "get", o1, null, emptyObjArray)
                            .toString());
            assertEquals("0",
                    callMethod(Inheritance, "get", o0, null, emptyObjArray)
                            .toString());
            assertEquals("1",
                    callMethod(Inheritance, "get", om1, null, emptyObjArray)
                            .toString());
            assertEquals("17",
                    callMethod(Inheritance, "get", o17, null, emptyObjArray)
                            .toString());

            // Test "equals" of StringContainer
            List<TestData<Boolean>> testEquals1 = Arrays.asList(
                    new TestData<Boolean>(true, o1, o1),
                    new TestData<Boolean>(true, o1, om1),
                    new TestData<Boolean>(false, o1, o0),
                    new TestData<Boolean>(false, om1, o0),
                    new TestData<Boolean>(false, o17, o17));

            runTests(Inheritance, "equals", new Class<?>[] { Object.class },
                    testEquals1);

            // Set, and test "equals" again
            callMethod(Inheritance, "set", o0, new Class<?>[] { int.class }, 1);
            callMethod(Inheritance, "set", o17, new Class<?>[] { int.class },
                    16);

            List<TestData<Boolean>> testEquals2 = Arrays.asList(
                    new TestData<Boolean>(true, o1, o1),
                    new TestData<Boolean>(true, o1, om1),
                    new TestData<Boolean>(true, o1, o0),
                    new TestData<Boolean>(true, om1, o0),
                    new TestData<Boolean>(true, o17, o17));

            runTests(Inheritance, "equals", new Class<?>[] { Object.class },
                    testEquals2);

            // Test zeroInstance() of SuperClass
            Object zeroNatWrap = callMethod(SuperClass, "zeroInstance", null,
                    null, emptyObjArray);
            assertEquals(0, callMethod(NatWrapper, "get", zeroNatWrap, null,
                    emptyObjArray));

            // Test zeroInstance() of Inheritance
            Object zeroInheritance = callMethod(Inheritance, "zeroInstance",
                    null, null, emptyObjArray);
            zeroNatWrap = callMethod(Inheritance, "get", zeroInheritance, null,
                    emptyObjArray);
            assertEquals(0, callMethod(NatWrapper, "get", zeroNatWrap, null,
                    emptyObjArray));

        } catch (NoSuchMethodException | SecurityException
                | InstantiationException | IllegalAccessException
                | IllegalArgumentException | InvocationTargetException e) {
            e.printStackTrace();
            fail(e.getMessage());
        }

    }

}
