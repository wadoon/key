package de.tud.cs.se.ds.psec.compiler;

import java.util.Arrays;
import java.util.List;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;

/**
 * Functional test cases for the compiler (i.e., Java code is compiled,
 * executed, and tested for correctness).
 *
 * @author Dominic Scheurer
 */
public class ComplexLoopsFunctionalTests
        extends AbstractCompilerFunctionalTest {
    private static final boolean DELETE_TMP_FILES = false;
    
    // Let tests time out after 15 seconds.
//    @Rule
//    public Timeout globalTimeout = Timeout.millis(15000);

    public ComplexLoopsFunctionalTests() {
        super(DELETE_TMP_FILES);
    }

    /**
     * This test case is subsumed by
     * {@link #testWhileWithNestedLoopsAndContinue()}, but if the more complex
     * one fails, this one can be another benchmark.
     */
    @Test
    public void testWhileLoopWithOneBreak() {

        List<TestData<Integer>> testData = Arrays.asList(
                new TestData<Integer>(0, null, 10),
                new TestData<Integer>(0, null, 100),
                new TestData<Integer>(0, null, 42),
                new TestData<Integer>(-1, null, -1),
                new TestData<Integer>(0, null, 3));

        //@formatter:off
        compileAndTest(
                "complex_loops/one_break_or_continue/WhileWithOneBreak.java",
                "de.tud.test.complex_loops.WhileWithOneBreak",
                "testSimpleBreak",
                new Class<?>[] { int.class },
                testData);
        //@formatter:on

    }

    /**
     * This test case is subsumed by
     * {@link #testWhileWithNestedLoopsAndContinue()}, but if the more complex
     * one fails, this one can be another benchmark.
     */
    @Test
    public void testWhileLoopWithOneContinue() {

        List<TestData<Integer>> testData = Arrays.asList(
                new TestData<Integer>(0, null, 10),
                new TestData<Integer>(0, null, 100),
                new TestData<Integer>(0, null, 42),
                new TestData<Integer>(-1, null, -1));

        //@formatter:off
        compileAndTest(
                "complex_loops/one_break_or_continue/WhileWithOneContinue.java",
                "de.tud.test.complex_loops.WhileWithOneContinue",
                "test",
                new Class<?>[] { int.class },
                testData);
        //@formatter:on

    }

    /**
     * This test case is subsumed by
     * {@link #testWhileWithNestedLoopsAndContinue()}, but if the more complex
     * one fails, this one can be another benchmark.
     */
    @Test
    public void testWhileLoopWithTwoBreaksOneNested() {

        List<TestData<Integer>> testData = Arrays.asList(
                new TestData<Integer>(0, null, 10),
                new TestData<Integer>(0, null, 100),
                new TestData<Integer>(0, null, 42),
                new TestData<Integer>(-1, null, -1));

        //@formatter:off
        compileAndTest(
                "complex_loops/one_nested_break/WhileWithTwoAndNestedBreaks.java",
                "de.tud.test.complex_loops.WhileWithTwoAndNestedBreaks",
                "testNestedLoopComplexBreak",
                new Class<?>[] { int.class },
                testData);
        //@formatter:on

    }

    @Test
    public void testWhileWithNestedLoopsAndContinue() {

        List<TestData<Integer>> testData = Arrays.asList(
                new TestData<Integer>(0, null, 10),
                new TestData<Integer>(0, null, 100),
                new TestData<Integer>(0, null, 42),
                new TestData<Integer>(-1, null, -1));

        //@formatter:off
        compileAndTest(
                "complex_loops/nested_multiple_break_continue/WhileWithNestedLoopsAndContinue.java",
                "de.tud.test.complex_loops.WhileWithNestedLoopsAndContinue",
                "test",
                new Class<?>[] { int.class },
                testData);
        //@formatter:on

    }

}
