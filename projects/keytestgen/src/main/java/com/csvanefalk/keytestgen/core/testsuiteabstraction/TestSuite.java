package com.csvanefalk.keytestgen.core.testsuiteabstraction;

import com.csvanefalk.keytestgen.core.CoreException;
import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaClass;
import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaMethod;

import java.util.LinkedList;
import java.util.List;

/**
 * Instances of this class represent a Test Suite, that is, a set of
 * {@link TestCase} instances for a given {@link KeYJavaMethod}.
 *
 * @author christopher
 */
public class TestSuite {

    /**
     * Factory method for creating a {@link TestSuite} instance.
     *
     * @param javaClass the class containing the method associated with the test
     *                  suite.
     * @param method    the method associated with the test suite.
     * @param testCases the {@link TestCase} instances associated with the test suite.
     * @return the test suite.
     * @throws CoreException
     */
    public static TestSuite constructTestSuite(final KeYJavaClass javaClass,
                                               final KeYJavaMethod method,
                                               final List<TestCase> testCases) throws CoreException {

        /*
         * Verify that each provided test case belongs to the same exact method
         * instance as the test suite itself.
         */
        for (final TestCase testCase : testCases) {

            final KeYJavaMethod testCaseMethod = testCase.getMethod();
            if (testCaseMethod != method) {
                throw new CoreException(
                        "Attempted to add abstract test case to an abstract test suite belonging to a different method");
            }
        }

        return new TestSuite(javaClass, method, testCases);
    }

    /**
     * The class for which this TestSuite is testing a method.
     */
    private final KeYJavaClass javaClass;

    /**
     * The method the test cases in this suite have been created for,
     * represented by a {@link KeYJavaMethod} instance.
     */
    private final KeYJavaMethod method;

    /**
     * The set of test cases contained in this suite.
     */
    private final List<TestCase> testCases = new LinkedList<TestCase>();

    private TestSuite(final KeYJavaClass javaClass, final KeYJavaMethod method, final List<TestCase> testCases) {

        this.javaClass = javaClass;
        this.method = method;
        this.testCases.addAll(testCases);
    }

    /**
     * @return the {@link KeYJavaClass} associated with this test suite.
     */
    public KeYJavaClass getJavaClass() {
        return javaClass;
    }

    /**
     * @return the method this test suite contains test cases for.
     */
    public KeYJavaMethod getMethod() {
        return method;
    }

    /**
     * @return the test cases contained in this test suite.
     */
    public List<TestCase> getTestCases() {
        return testCases;
    }
}
