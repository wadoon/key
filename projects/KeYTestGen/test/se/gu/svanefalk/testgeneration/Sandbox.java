package se.gu.svanefalk.testgeneration;

import java.io.IOException;
import java.util.List;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.backend.xml.XMLGeneratorException;
import se.gu.svanefalk.testgeneration.core.model.ModelGeneratorException;
import se.gu.svanefalk.testgeneration.util.transformers.TermTransformerException;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.smt.IllegalFormulaException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class Sandbox extends KeYTestGenTest {

    private final String containerTypeName = "PrimitiveIntegerOperations";
    private final String javaPathInBaseDir = "/home/christopher/git/key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> getEnvironmentForMethod(
            final String method) throws ProofInputException,
            ModelGeneratorException, IOException, ProblemLoaderException {

        return getPreparedEnvironment(
                AbstractSymbolicExecutionTestCase.keyRepDirectory,
                javaPathInBaseDir, containerTypeName, method, null, false);
    }

    @Test
    public void test() throws ProofInputException, ModelGeneratorException,
            IOException, XMLGeneratorException, ProblemLoaderException,
            IllegalFormulaException, TermTransformerException {

        final String method = "doStuff";
        final SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment = getEnvironmentForMethod(method);

        final List<IExecutionNode> nodes = retrieveNode(
                environment.getBuilder().getStartNode(), "x=1");

        for (final IExecutionNode node : nodes) {

            System.out.println(node.getFormatedPathCondition());
        }
    }
}