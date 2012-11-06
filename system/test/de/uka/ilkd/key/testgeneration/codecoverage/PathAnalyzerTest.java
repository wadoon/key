package de.uka.ilkd.key.testgeneration.codecoverage;

import java.io.IOException;

import org.junit.Test;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.KeYTestGenTest;
import de.uka.ilkd.key.testgeneration.model.modelgeneration.ModelGeneratorException;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class PathAnalyzerTest
        extends KeYTestGenTest {

    private final String javaPathInBaseDir =
            "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private final String containerTypeName = "PrimitiveIntegerOperations";

    @Test
    public void test() throws ProofInputException, ModelGeneratorException, IOException {

        String method = "max";
        SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment =
                getEnvironmentForMethod(method);

        printSymbolicExecutionTree(environment.getBuilder().getStartNode());

    }

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> getEnvironmentForMethod(
            String method) throws ProofInputException, ModelGeneratorException, IOException {

        return getPreparedEnvironment(keyRepDirectory, javaPathInBaseDir, containerTypeName,
                method, null, false);
    }

}
