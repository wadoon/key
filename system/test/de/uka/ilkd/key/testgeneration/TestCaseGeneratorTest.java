package de.uka.ilkd.key.testgeneration;

import static org.junit.Assert.*;

import java.io.File;
import java.io.IOException;
import java.util.Map.Entry;

import org.junit.Test;

import de.uka.ilkd.key.java.statement.Assert;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.testgeneration.backend.TestGeneratorException;
import de.uka.ilkd.key.testgeneration.backend.xml.XMLGeneratorException;
import de.uka.ilkd.key.testgeneration.backend.xml.XMLTestCaseGenerator;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.util.Benchmark;

public class TestCaseGeneratorTest {

    @Test
    public void test() throws IOException, ProofInputException,
            ModelGeneratorException, TestGeneratorException,
            KeYInterfaceException, XMLGeneratorException, InterruptedException {

        assertTrue(new File("/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java").exists());
        
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