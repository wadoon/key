package de.tud.cs.se.ds.psec.compiler;

import java.util.Arrays;
import java.util.List;

import org.junit.Test;

/**
 * Functional test cases for the compiler (i.e., Java code is compiled,
 * executed, and tested for correctness).
 *
 * @author Dominic Scheurer
 */
public class ComplexLoopsFunctionalTests
        extends AbstractCompilerFunctionalTest {
    private static final boolean DELETE_TMP_FILES = false;

    public ComplexLoopsFunctionalTests() {
        super(DELETE_TMP_FILES);
    }

    /**
     * This test case is subsumed by
     * {@link #testWhileLoopWithContinueAndInnerLoop()}, but if the more complex
     * one fails, this one can be another benchmark.
     */
    @Test
    public void testWhileLoopWithOneBreak() {

        List<TestData<Integer>> testData = Arrays.asList(
                new TestData<Integer>(0, null, 10),
                new TestData<Integer>(0, null, 100),
                new TestData<Integer>(0, null, 42),
                new TestData<Integer>(-1, null, -1));

        //@formatter:off
        compileAndTest(
                "complex_loops/one_break_or_continue/WhileWithBreaks.java",
                "de.tud.test.complex_loops.WhileWithBreaks",
                "testSimpleBreak",
                new Class<?>[] { int.class },
                testData);
        //@formatter:on

    }

    /**
     * This test case is subsumed by
     * {@link #testWhileLoopWithContinueAndInnerLoop()}, but if the more complex
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
     * {@link #testWhileLoopWithContinueAndInnerLoop()}, but if the more complex
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
    public void testWhileLoopWithContinueAndInnerLoop() {

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
