package com.csvanefalk.keytestgen.backend;

public interface ITestSuite {

    int getTestMethods();

    String getClassName();

    String getPackage();

    String getTestSuiteBody();
}
