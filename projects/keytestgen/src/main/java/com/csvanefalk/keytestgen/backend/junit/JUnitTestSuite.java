package com.csvanefalk.keytestgen.backend.junit;

import com.csvanefalk.keytestgen.backend.ITestSuite;
import com.csvanefalk.keytestgen.core.testsuiteabstraction.TestSuite;

public class JUnitTestSuite implements ITestSuite {

    private final TestSuite testSuite;
    private final String body;
    private final String name;

    public JUnitTestSuite(TestSuite testSuite, String name, String body) {
        this.testSuite = testSuite;
        this.body = body;
        this.name = name;
    }

    public JUnitTestSuite(TestSuite testSuite, String body) {
        this.testSuite = testSuite;
        this.body = body;
        /*
         * Construct the name of the test suite
         */
        String className = testSuite.getJavaClass().getName();
        String methodName = testSuite.getMethod().getName();

        // make the first letter of the method name capital
        char firstLetter = Character.toUpperCase(methodName.charAt(0));
        if (methodName.length() > 1) {
            methodName = firstLetter + methodName.substring(1);
        } else {
            methodName = firstLetter + "";
        }

        this.name = "Test" + className + methodName;
    }

    @Override
    public String getTestSuiteBody() {
        return body;
    }

    @Override
    public int getTestMethods() {
        return 0;
    }

    @Override
    public String getClassName() {
        return name;
    }

    @Override
    public String getPackage() {
        return testSuite.getJavaClass().getPackageDeclaration();
    }
}
