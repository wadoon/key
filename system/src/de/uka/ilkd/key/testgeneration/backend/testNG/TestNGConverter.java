package de.uka.ilkd.key.testgeneration.backend.testNG;

import java.util.List;

import de.uka.ilkd.key.testgeneration.backend.AbstractJavaSourceGenerator;
import de.uka.ilkd.key.testgeneration.backend.IFrameworkConverter;
import de.uka.ilkd.key.testgeneration.backend.junit.JUnitConverter;
import de.uka.ilkd.key.testgeneration.core.coreinterface.TestCase;
import de.uka.ilkd.key.testgeneration.core.coreinterface.TestSuite;

/**
 * This singleton provides the functionality needed to produce test suites for
 * the TestNG framework.
 * 
 * @author christopher
 * 
 */
public final class TestNGConverter implements IFrameworkConverter {

    public String generateTestNGSources(List<TestCase> testCases) {

        return null;
    }

    /**
     * Worker which services invocations of
     * {@link JUnitConverter#convertToJUnit(List)}.
     * 
     * @author christopher
     * 
     */
    private static class TestNGGeneratorWorker extends
            AbstractJavaSourceGenerator {

        public String serviceConvert(TestSuite testSuite) {

            return null;
        }
    }

    @Override
    public String convert(TestSuite testSuite) {
        // TODO Auto-generated method stub
        return null;
    }
}
