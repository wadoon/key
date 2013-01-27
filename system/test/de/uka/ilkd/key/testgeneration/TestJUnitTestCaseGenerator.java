package de.uka.ilkd.key.testgeneration;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.util.Map.Entry;

import org.junit.BeforeClass;
import org.junit.Test;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.testgeneration.backend.ITestCaseGenerator;
import de.uka.ilkd.key.testgeneration.backend.TestGeneratorException;
import de.uka.ilkd.key.testgeneration.backend.junit.JUnitTestCaseGenerator;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.util.Benchmark;
import de.uka.ilkd.key.testgeneration.xml.XMLGeneratorException;

public class TestJUnitTestCaseGenerator {
    
    @BeforeClass
    public static void buildUp() throws ClassNotFoundException {
        
        System.out.println("GOT IT!");
        
       //System.out.println(Class.forName("de.uka.ilkd.key.testgeneration.targetmodels.PrimitiveIntegerOperations"));
        
    }
    
    @Test
    public void test() throws IOException, ProofInputException,
            ModelGeneratorException, TestGeneratorException,
            KeYInterfaceException, XMLGeneratorException, InterruptedException {

        assertTrue(new File("/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java").exists());
        
        ITestCaseGenerator testCaseGenerator = new JUnitTestCaseGenerator();
        String output = testCaseGenerator
                .generatePartialTestSuite(
                        "/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java",
                        null, "max");

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
