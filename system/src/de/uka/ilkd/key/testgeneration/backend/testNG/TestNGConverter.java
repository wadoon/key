package de.uka.ilkd.key.testgeneration.backend.testNG;

import java.util.List;

import de.uka.ilkd.key.testgeneration.backend.IFrameworkConverter;
import de.uka.ilkd.key.testgeneration.core.testsuiteabstraction.TestCase;
import de.uka.ilkd.key.testgeneration.core.testsuiteabstraction.TestSuite;

/**
 * This singleton provides the functionality needed to produce test suites for
 * the TestNG framework.
 * 
 * @author christopher
 * 
 */
public final class TestNGConverter implements IFrameworkConverter {

    @Override
    public String convert(final TestSuite testSuite) {
        // TODO Auto-generated method stub
        return null;
    }

    public String generateTestNGSources(final List<TestCase> testCases) {

        return null;
    }
}
