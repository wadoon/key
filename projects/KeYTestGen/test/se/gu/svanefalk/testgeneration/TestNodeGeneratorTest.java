package se.gu.svanefalk.testgeneration;

import java.io.IOException;
import java.util.List;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.backend.junit.JUnitConverter;
import se.gu.svanefalk.testgeneration.core.NodeTestGenerator;
import se.gu.svanefalk.testgeneration.core.model.IModelGenerator;
import se.gu.svanefalk.testgeneration.core.model.ModelGeneratorException;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelGenerator;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class TestNodeGeneratorTest extends KeYTestGenTest {

    private final String containerTypeName = "PrimitiveIntegerOperations";
    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment;
    private final String javaPathInBaseDir = "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private IModelGenerator modelGenerator;

    private void setup(final String method) throws ProofInputException,
            ModelGeneratorException, IOException, ProblemLoaderException {

        if (modelGenerator == null) {
            modelGenerator = ModelGenerator.INSTANCE;
        }

        environment = getPreparedEnvironment(
                AbstractSymbolicExecutionTestCase.keyRepDirectory,
                javaPathInBaseDir, containerTypeName, method, null, false);
    }

    /**
     * Test model instantiation for the standard mid method.
     * 
     * @throws Exception
     */
    @Test
    public void testMid() throws Exception {

        setup("mid");
        final IExecutionStartNode root = environment.getBuilder().getStartNode();
        final List<IExecutionNode> nodes = retrieveNode(root, "mid=x");

        for (final IExecutionNode node : nodes) {
            NodeTestGenerator.INSTANCE.constructTestSuiteFromNode(node,
                    new JUnitConverter());
        }
    }
}
