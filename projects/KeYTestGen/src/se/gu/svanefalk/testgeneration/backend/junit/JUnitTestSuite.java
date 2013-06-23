package se.gu.svanefalk.testgeneration.backend.junit;

import se.gu.svanefalk.testgeneration.backend.ITestSuite;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestSuite;

public class JUnitTestSuite implements ITestSuite {

    private final TestSuite testSuite;
    private final String body;
    private final String name;

    public JUnitTestSuite(TestSuite testSuite, String body) {
        super();
        this.testSuite = testSuite;
        this.body = body;

        /*
         * Construct the name of the test suite
         */
        String name = "";
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
        return testSuite.getJavaClass().getPackageDeclaration().toString();
    }
}
