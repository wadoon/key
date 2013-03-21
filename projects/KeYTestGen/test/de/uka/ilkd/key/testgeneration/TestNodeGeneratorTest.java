package de.uka.ilkd.key.testgeneration;

import java.io.IOException;
import java.util.List;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.core.NodeTestGenerator;
import se.gu.svanefalk.testgeneration.core.model.IModelGenerator;
import se.gu.svanefalk.testgeneration.core.model.ModelGeneratorException;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelGenerator;

import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class TestNodeGeneratorTest extends KeYTestGenTest {

    private IModelGenerator modelGenerator;
    private final String javaPathInBaseDir = "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private final String containerTypeName = "PrimitiveIntegerOperations";
    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment;

    /**
     * Test model instantiation for the standard mid method.
     * 
     * @throws Exception
     */
    @Test
    public void testMid() throws Exception {

        setup("mid");
        IExecutionStartNode root = environment.getBuilder().getStartNode();
        List<IExecutionNode> nodes = retrieveNode(root, "mid=x");

        for (IExecutionNode node : nodes) {
            NodeTestGenerator.INSTANCE.constructTestSuiteFromNode(node);
        }
    }

    private void setup(String method) throws ProofInputException,
            ModelGeneratorException, IOException, ProblemLoaderException {

        if (modelGenerator == null) {
            modelGenerator = ModelGenerator.INSTANCE;
        }

        environment = getPreparedEnvironment(keyRepDirectory,
                javaPathInBaseDir, containerTypeName, method, null, false);
    }
}
