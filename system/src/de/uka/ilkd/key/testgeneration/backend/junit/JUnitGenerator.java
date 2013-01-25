package de.uka.ilkd.key.testgeneration.backend.junit;

import java.util.List;

import de.uka.ilkd.key.testgeneration.backend.AbstractJavaSourceGenerator;
import de.uka.ilkd.key.testgeneration.backend.TestCase;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaClass;

/**
 * This singleton provides the functionality needed to produce test suites for
 * the JUnit framework.
 * 
 * @author christopher
 * 
 */
public class JUnitGenerator {

    public String generateJUnitSources(KeYJavaClass klass,
            List<TestCase> testCases) {

        return new JUnitGeneratorWorker().serviceConvertToJUnit(klass, testCases);
    }

    /**
     * Worker which services invocations of
     * {@link JUnitGenerator#convertToJUnit(List)}.
     * 
     * @author christopher
     * 
     */
    private static class JUnitGeneratorWorker extends
            AbstractJavaSourceGenerator {

        public String serviceConvertToJUnit(KeYJavaClass klass,
                List<TestCase> testCases) {

            /*
             * Print the class header
             */
            
            for (TestCase testCase : testCases) {
                
            }

            return null;
        }
    }
}