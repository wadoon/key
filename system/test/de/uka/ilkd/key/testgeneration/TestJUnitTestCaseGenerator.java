package de.uka.ilkd.key.testgeneration;



import java.io.File;
import java.io.IOException;
import java.util.Map.Entry;

import org.junit.*;


import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.testgeneration.backend.ITestCaseGenerator;
import de.uka.ilkd.key.testgeneration.backend.TestGeneratorException;
import de.uka.ilkd.key.testgeneration.backend.junit.JUnitTestCaseGenerator;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.core.xml.XMLGeneratorException;
import de.uka.ilkd.key.testgeneration.util.Benchmark;

public class TestJUnitTestCaseGenerator {
    
    
    @Test
    public void test() throws IOException, ProofInputException,
            ModelGeneratorException, TestGeneratorException,
            KeYInterfaceException, XMLGeneratorException, InterruptedException {

        Assert.assertTrue(new File("/home/christopher/git/key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java").exists());
        
        ITestCaseGenerator testCaseGenerator = new JUnitTestCaseGenerator();
   
        String output = testCaseGenerator
                .generatePartialTestSuite(
                        "/home/christopher/git/key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java",
                        null, "midOneProxyOneInstance");

        /*
        String output = testCaseGenerator
                .generatePartialTestSuite(
                        "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java",
                        null, "midOneProxyOneInstance");
*/
        for (Entry<String, Long> entry : Benchmark.getReadings().entrySet()) {
            System.out.println(entry.getKey() + " : " + entry.getValue()
                    + " milliseconds");
        }
        System.out.println(output);
    }
    
    private <T> T get(Object o) {
        return (T)o;
    }

}
