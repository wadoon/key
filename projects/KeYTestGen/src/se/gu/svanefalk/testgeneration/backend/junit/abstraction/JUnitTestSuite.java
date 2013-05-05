package se.gu.svanefalk.testgeneration.backend.junit.abstraction;

import java.util.LinkedList;
import java.util.List;

import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestSuite;

/**
 * Represents a JUnit test suite. It consists of a set of {@link JUnitTestCase}
 * instances, a set of imports, and a set of utility methods and state
 * variables.
 * 
 * @author christopher
 * 
 */
public class JUnitTestSuite {

    /**
     * The imports needed for this test suite.
     */
    private final List<String> imports = new LinkedList<String>();

    /**
     * The test cases belonging to this test suite.
     */
    private final List<JUnitTestCase> testCases = new LinkedList<JUnitTestCase>();

    /**
     * Constructs a JUnit test suite from an abstract {@link TestSuite}.
     * 
     * @param testSuite
     */
    public JUnitTestSuite(final TestSuite testSuite) {

    }

    /**
     * Adds an import to the test suite.
     * 
     * @param declarationStatement
     * 
     */
    public void addImport(final String importStatement) {
        imports.add(importStatement);
    }

    /**
     * Adds a {@link JUnitTestCase} to the test suite.
     * 
     * @param declarationStatement
     * 
     */
    public void addTestCase(final JUnitTestCase testCase) {
        testCases.add(testCase);
    }

    /**
     * @return the imports
     */
    public List<String> getImports() {
        return imports;
    }

    /**
     * @return the testCases
     */
    public List<JUnitTestCase> getTestCases() {
        return testCases;
    }
}