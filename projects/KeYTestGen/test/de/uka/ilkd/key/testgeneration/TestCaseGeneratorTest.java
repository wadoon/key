package de.uka.ilkd.key.testgeneration;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.util.Map.Entry;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.backend.TestGeneratorException;
import se.gu.svanefalk.testgeneration.backend.xml.XMLGeneratorException;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.core.model.ModelGeneratorException;
import se.gu.svanefalk.testgeneration.util.Benchmark;

import de.uka.ilkd.key.proof.init.ProofInputException;

public class TestCaseGeneratorTest {

    @Test
    public void test() throws IOException, ProofInputException,
            ModelGeneratorException, TestGeneratorException,
            KeYInterfaceException, XMLGeneratorException, InterruptedException {

        assertTrue(new File(
                "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java")
                .exists());

        XMLTestCaseGenerator testCaseGenerator = XMLTestCaseGenerator
                .getDefaultInstance();
        String output = testCaseGenerator
                .generatePartialTestSuite(
                        "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java",
                        null, "midOneProxyOneInstance");

        for (Entry<String, Long> entry : Benchmark.getReadings().entrySet()) {
            System.out.println(entry.getKey() + " : " + entry.getValue()
                    + " milliseconds");
        }
        System.out.println(output);
    }
}