package com.csvanefalk.keytestgen.backend.testNG;

import com.csvanefalk.keytestgen.backend.IFrameworkConverter;
import com.csvanefalk.keytestgen.core.testsuiteabstraction.TestCase;
import com.csvanefalk.keytestgen.core.testsuiteabstraction.TestSuite;

import java.util.List;

/**
 * This singleton provides the functionality needed to produce test suites for
 * the TestNG framework.
 *
 * @author christopher
 */
public final class TestNGConverter implements IFrameworkConverter {

    @Override
    public TestNGTestSuite convert(final TestSuite testSuite) {
        // TODO Auto-generated method stub
        return null;
    }

    public String generateTestNGSources(final List<TestCase> testCases) {

        return null;
    }
}
