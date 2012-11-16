package de.uka.ilkd.key.testgeneration;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.DefaultProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class Sandbox {

    @Test
    public void test() throws IOException, ProofInputException, ModelGeneratorException {
        File file = new File("/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java");
        File javaFile = new File(file, "PrimitiveIntegerOperations.java");

        TestCaseGenerator testCaseGenerator = TestCaseGenerator.getDefaultInstance();
        String stuff = testCaseGenerator.generateTestCase(new stuff<String>(), null, null);
    }
    
}


class stuff<String> implements ITestCaseParser<String> {

    @Override
    public String generateTestCaseFromXML(java.lang.String representation) {

        // TODO Auto-generated method stub
        return null;
    }
    
}