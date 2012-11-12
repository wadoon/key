package de.uka.ilkd.key.testgeneration.oraclegeneration;

import java.io.IOException;

import org.junit.Test;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.KeYTestGenTest;
import de.uka.ilkd.key.testgeneration.model.modelgeneration.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.visitors.XMLVisitorException;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class OracleGeneratorTest
        extends KeYTestGenTest {

    private final String javaPathInBaseDir =
            "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private final String containerTypeName = "PrimitiveIntegerOperations";

    @Test
    public void testPostConditionExtraction() throws ProofInputException, ModelGeneratorException, IOException, OracleGeneratorException, XMLVisitorException {

        String method = "max";
        SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment =
                getEnvironmentForMethod(method);

        IExecutionStartNode root = environment.getBuilder().getStartNode();
       
        OracleGenerator generator = new OracleGenerator();
        
        IExecutionMethodCall call;
        
       generator.extractPostCondition(root);
    }

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> getEnvironmentForMethod(
            String method) throws ProofInputException, ModelGeneratorException, IOException {

        return getPreparedEnvironment(keyRepDirectory, javaPathInBaseDir, containerTypeName,
                method, null, false);
    }
}
