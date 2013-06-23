package se.gu.svanefalk.testgeneration.backend;

public interface ITestSuite {

    int getTestMethods();

    String getClassName();

    String getPackage();

    String getTestSuiteBody();
}
