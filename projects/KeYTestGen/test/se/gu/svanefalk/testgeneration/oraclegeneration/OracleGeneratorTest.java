package se.gu.svanefalk.testgeneration.oraclegeneration;

import java.io.IOException;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.KeYTestGenTest;
import se.gu.svanefalk.testgeneration.core.model.ModelGeneratorException;
import se.gu.svanefalk.testgeneration.core.oracle.OracleGeneratorException;
import se.gu.svanefalk.testgeneration.util.parsers.visitors.XMLVisitorException;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class OracleGeneratorTest extends KeYTestGenTest {

    private final String containerTypeName = "PrimitiveIntegerOperations";
    private final String javaPathInBaseDir = "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> getEnvironmentForMethod(
            final String method) throws ProofInputException,
            ModelGeneratorException, IOException, ProblemLoaderException {

        return getPreparedEnvironment(
                AbstractSymbolicExecutionTestCase.keyRepDirectory,
                javaPathInBaseDir, containerTypeName, method, null, false);
    }

    @Test
    public void testPostConditionExtraction() throws ProofInputException,
            ModelGeneratorException, IOException, OracleGeneratorException,
            XMLVisitorException, ProblemLoaderException {

        final String method = "max";
        final SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment = getEnvironmentForMethod(method);

        environment.getBuilder().getStartNode();

    }
}
