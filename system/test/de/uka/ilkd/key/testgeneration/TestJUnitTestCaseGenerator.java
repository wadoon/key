package de.uka.ilkd.key.testgeneration;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.Map.Entry;

import org.junit.Assert;
import org.junit.Test;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.testgeneration.backend.IFrameworkConverter;
import de.uka.ilkd.key.testgeneration.backend.TestGenerator;
import de.uka.ilkd.key.testgeneration.backend.TestGeneratorException;
import de.uka.ilkd.key.testgeneration.backend.junit.JUnitConverter;
import de.uka.ilkd.key.testgeneration.backend.xml.XMLGeneratorException;
import de.uka.ilkd.key.testgeneration.core.codecoverage.ICodeCoverageParser;
import de.uka.ilkd.key.testgeneration.core.codecoverage.implementation.StatementCoverageParser;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.util.Benchmark;

public class TestJUnitTestCaseGenerator {

    @Test
    public void test() throws IOException, ProofInputException,
            ModelGeneratorException, TestGeneratorException,
            KeYInterfaceException, XMLGeneratorException, InterruptedException {

        Assert.assertTrue(new File(
                "/home/christopher/git/key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java")
                .exists());

        TestGenerator testCaseGenerator = TestGenerator.INSTANCE;
        IFrameworkConverter junitConverter = new JUnitConverter();
        ICodeCoverageParser codeCoverageParser = new StatementCoverageParser();

        List<String> output = testCaseGenerator
                .generatePartialTestSuite(
                        "/home/christopher/git/key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java",
                        codeCoverageParser, junitConverter, "mid");

        /*
         * String output = testCaseGenerator .generatePartialTestSuite(
         * "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java"
         * , null, "midOneProxyOneInstance");
         */
        for (Entry<String, Long> entry : Benchmark.getReadings().entrySet()) {
            System.out.println(entry.getKey() + " : " + entry.getValue()
                    + " milliseconds");
        }
        System.out.println(output);
    }

    private <T> T get(Object o) {
        return (T) o;
    }
}
