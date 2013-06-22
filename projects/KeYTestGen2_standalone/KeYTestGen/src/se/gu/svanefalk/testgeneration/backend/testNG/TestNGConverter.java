package se.gu.svanefalk.testgeneration.backend.testNG;

import java.util.List;

import se.gu.svanefalk.testgeneration.backend.IFrameworkConverter;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestCase;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestSuite;

/**
 * This singleton provides the functionality needed to produce test suites for
 * the TestNG framework.
 * 
 * @author christopher
 * 
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
