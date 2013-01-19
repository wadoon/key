package de.uka.ilkd.key.testgeneration;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Map;

import org.junit.Test;

import de.uka.ilkd.key.keynterpol.EmbeddedModelGenerator;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.model.IModel;
import de.uka.ilkd.key.testgeneration.model.IModelGenerator;
import de.uka.ilkd.key.testgeneration.model.IModelObject;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelGenerator;
import de.uka.ilkd.key.testgeneration.targetmodels.PrimitiveIntegerOperations;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class TestEmbeddedSMTModelGeneration
        extends KeYTestGenTest {

    private IModelGenerator modelGenerator;
    private final String javaPathInBaseDir =
            "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
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
        testMid("x");
        testMid("y");
        testMid("z");
    }

    /**
     * Test various return values for the mid method.
     * 
     * @param variable
     *            - can be x, y or z. See signature for mid.
     * @throws Exception
     */
    private void testMid(String variable) throws Exception {

        ArrayList<IExecutionNode> nodes =
                retrieveNode(environment.getBuilder().getStartNode(), "mid=" + variable);

        /*
         * For each node, generate a model for it, refine that model, and then use the resulting
         * fixture in order to run the method under test and assert correct results.
         */
        for (IExecutionNode node : nodes) {

            System.out.println("Mid " + variable);
            printSingleNode(node);

            IModel model = modelGenerator.generateModel(node);

            Map<String, ? extends IModelObject> variableMapping =
                    model.getVariableNameMapping();

            int x = (Integer) variableMapping.get("x").getValue();
            int y = (Integer) variableMapping.get("y").getValue();
            int z = (Integer) variableMapping.get("z").getValue();
            int result = PrimitiveIntegerOperations.mid(x, y, z);

            System.out.println("Satisfiable assignment: x=" + x + " y=" + y + " z=" + z);

            assertTrue(result == (Integer) variableMapping.get(variable).getValue());
        }
    }

    private void setup(String method)
            throws ProofInputException, ModelGeneratorException, IOException,
            ProblemLoaderException {

        if (modelGenerator == null) {
            modelGenerator = new EmbeddedModelGenerator();
        }

        environment =
                getPreparedEnvironment(keyRepDirectory, javaPathInBaseDir,
                        containerTypeName, method, null, false);
    }

    private interface IFunctionDelegate {

        public <T> T apply(T... args);
    }
}
