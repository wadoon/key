package de.uka.ilkd.key.testgeneration.oraclegeneration;

import java.io.IOException;

import org.junit.Test;

import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.KeYTestGenTest;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.core.oracle.OracleGeneratorException;
import de.uka.ilkd.key.testgeneration.util.parsers.visitors.XMLVisitorException;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class OracleGeneratorTest extends KeYTestGenTest {

    private final String javaPathInBaseDir = "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private final String containerTypeName = "PrimitiveIntegerOperations";

    @Test
    public void testPostConditionExtraction() throws ProofInputException,
            ModelGeneratorException, IOException, OracleGeneratorException,
            XMLVisitorException, ProblemLoaderException {

        String method = "max";
        SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment = getEnvironmentForMethod(method);

        IExecutionStartNode root = environment.getBuilder().getStartNode();

        IExecutionMethodCall call;

    }

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> getEnvironmentForMethod(
            String method) throws ProofInputException, ModelGeneratorException,
            IOException, ProblemLoaderException {

        return getPreparedEnvironment(keyRepDirectory, javaPathInBaseDir,
                containerTypeName, method, null, false);
    }
}
