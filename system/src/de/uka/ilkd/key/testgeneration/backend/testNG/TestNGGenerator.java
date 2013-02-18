package de.uka.ilkd.key.testgeneration.backend.testNG;

import java.util.List;

import de.uka.ilkd.key.testgeneration.backend.AbstractJavaSourceGenerator;
import de.uka.ilkd.key.testgeneration.backend.junit.JUnitGenerator;
import de.uka.ilkd.key.testgeneration.core.coreinterface.TestCase;

/**
 * This singleton provides the functionality needed to produce test suites for
 * the TestNG framework.
 * 
 * @author christopher
 * 
 */
public final class TestNGGenerator {

    public String generateTestNGSources(List<TestCase> testCases) {

        return null;
    }

    /**
     * Worker which services invocations of
     * {@link JUnitGenerator#convertToJUnit(List)}.
     * 
     * @author christopher
     * 
     */
    private static class TestNGGeneratorWorker extends
            AbstractJavaSourceGenerator {

        public String serviceConvertToTestNG(List<TestCase> testCases) {

            return null;
        }
    }
}
