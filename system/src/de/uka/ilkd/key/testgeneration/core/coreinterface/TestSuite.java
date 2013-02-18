package de.uka.ilkd.key.testgeneration.core.coreinterface;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.testgeneration.core.KeYJavaMethod;

/**
 * Instances of this class represent a Test Suite, that is, a set of
 * {@link TestCase} instances for a given {@link KeYJavaMethod}.
 * 
 * @author christopher
 * 
 */
public class TestSuite {

    /**
     * The method the test cases in this suite have been created for,
     * represented by a {@link KeYJavaMethod} instance.
     */
    private final KeYJavaMethod method;

    /**
     * The set of test cases contained in this suite.
     */
    private final List<TestCase> testCases = new LinkedList<TestCase>();

    public TestSuite(final KeYJavaMethod method, final List<TestCase> testCases) {

        this.method = method;
        this.testCases.addAll(testCases);
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
