package de.uka.ilkd.key.testgeneration;

import java.io.File;
import java.io.IOException;
import java.util.Map.Entry;

import org.junit.Test;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.util.Benchmark;
import de.uka.ilkd.key.testgeneration.xml.XMLGeneratorException;

public class TestCaseGeneratorTest {

    @Test
    public void test() throws IOException, ProofInputException,
            ModelGeneratorException, TestGeneratorException,
            KeYInterfaceException, XMLGeneratorException, InterruptedException {

        XMLTestCaseGenerator testCaseGenerator = XMLTestCaseGenerator
                .getDefaultInstance();
        String output = testCaseGenerator
                .generateTestCase(
                        new File(
                                "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java"),
                        "midOneProxyOneInstance");

        for (Entry<String, Long> entry : Benchmark.getReadings().entrySet()) {
            System.out.println(entry.getKey() + " : " + entry.getValue()
                    + " milliseconds");
        }
        System.out.println(output);
    }
}