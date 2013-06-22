package se.gu.svanefalk.testgeneration.backend.junit;

import se.gu.svanefalk.testgeneration.backend.ITestSuite;

public class JUnitTestSuite implements ITestSuite {

    private final String name;
    private final String body;

    public JUnitTestSuite(String name, String body) {
        super();
        this.name = name;
        this.body = body;
    }

    @Override
    public String getTestSuiteName() {
        return name;
    }

    @Override
    public String getTestSuiteBody() {
        return body;
    }
}
