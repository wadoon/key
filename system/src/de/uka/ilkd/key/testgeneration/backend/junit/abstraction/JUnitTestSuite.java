package de.uka.ilkd.key.testgeneration.backend.junit.abstraction;

import java.util.LinkedList;
import java.util.List;

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
     * @return the testCases
     */
    public List<JUnitTestCase> getTestCases() {
        return testCases;
    }

    /**
     * Adds a {@link JUnitTestCase} to the test suite.
     * 
     * @param declarationStatement
     * 
     */
    public void addTestCase(JUnitTestCase testCase) {
        testCases.add(testCase);
    }

    /**
     * @return the imports
     */
    public List<String> getImports() {
        return imports;
    }

    /**
     * Adds an import to the test suite.
     * 
     * @param declarationStatement
     * 
     */
    public void addImport(String importStatement) {
        imports.add(importStatement);
    }
}