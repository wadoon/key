package de.uka.ilkd.key.testgeneration;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.defaultimplementation.IModelVariable;
import de.uka.ilkd.key.testgeneration.defaultimplementation.ModelGenerator;
import de.uka.ilkd.key.testgeneration.model.IModel;
import de.uka.ilkd.key.testgeneration.model.modelgeneration.IModelGenerator;
import de.uka.ilkd.key.testgeneration.model.modelgeneration.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.targetmodels.PrimitiveIntegerOperations;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Tests to assert that the model generation procedure generates fixtures
 * whichindeed cause specified execution paths to be taken. IMPORTANT - these
 * test cases involve heavy use of native program invocations, and might take
 * significant time to execute. To achieve this,
 * 
 * @author christopher
 */
public class TestModelGenerationIntegers
        extends KeYTestGenTest {

    private IModelGenerator modelGenerator;
    private final String javaPathInBaseDir =
            "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private final String containerTypeName = "PrimitiveIntegerOperations";

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment;

    @Before
    public void setup() throws ModelGeneratorException {

        // modelGenerator = ModelGenerator.getDefaultModelGenerator();
    }

    @Test
    public void testNonStaticMidOneExternalProxy() throws Exception {

        setup("nonStaticMidOneExternalProxy");

        // printSymbolicExecutionTreePathConditions(
        // environment.getBuilder().getStartNode());

        ArrayList<IExecutionNode> nodes =
                retrieveNode(environment.getBuilder().getStartNode(), "mid=y");

        for (IExecutionNode node : nodes) {

            System.out.println("nonStaticMidOneExternalProxy");
            printSingleNode(node);
        }

        /*
         * System.out.println(modelGenerator.generateNodeModel(node,
         * node.getServices())); HashMap<String, ValueContainer> model =
         * parseZ3Model(modelGenerator.generateNodeModel(node,
         * node.getServices())); printModel(model); int x =
         * (Integer)model.get("x").getValue(); int y =
         * (Integer)model.get("y").getValue(); int z =
         * (Integer)model.get("z").getValue(); int result =
         * PrimitiveIntegerOperations.mid(x,y,z); assertTrue(result ==
         * (Integer)model.get("y").getValue()); }
         */

    }

    @Test
    public void testNonStaticMidOneExternal() throws Exception {

        setup("nonStaticMidOneExternal");

        // printSymbolicExecutionTreePathConditions(
        // environment.getBuilder().getStartNode());

        ArrayList<IExecutionNode> nodes =
                retrieveNode(environment.getBuilder().getStartNode(), "mid=y");

        for (IExecutionNode node : nodes) {

            System.out.println("nonStaticMid");
            printSingleNode(node);
        }

        /*
         * System.out.println(modelGenerator.generateNodeModel(node,
         * node.getServices())); HashMap<String, ValueContainer> model =
         * parseZ3Model(modelGenerator.generateNodeModel(node,
         * node.getServices())); printModel(model); int x =
         * (Integer)model.get("x").getValue(); int y =
         * (Integer)model.get("y").getValue(); int z =
         * (Integer)model.get("z").getValue(); int result =
         * PrimitiveIntegerOperations.mid(x,y,z); assertTrue(result ==
         * (Integer)model.get("y").getValue()); }
         */

    }

    @Test
    public void testNonStaticMid() throws Exception {

        setup("nonStaticMid");

        // printSymbolicExecutionTreePathConditions(
        // environment.getBuilder().getStartNode());

        ArrayList<IExecutionNode> nodes =
                retrieveNode(environment.getBuilder().getStartNode(), "mid=y");

        for (IExecutionNode node : nodes) {

            System.out.println("nonStaticMid");
            printSingleNode(node);
        }

        /*
         * System.out.println(modelGenerator.generateNodeModel(node,
         * node.getServices())); HashMap<String, ValueContainer> model =
         * parseZ3Model(modelGenerator.generateNodeModel(node,
         * node.getServices())); printModel(model); int x =
         * (Integer)model.get("x").getValue(); int y =
         * (Integer)model.get("y").getValue(); int z =
         * (Integer)model.get("z").getValue(); int result =
         * PrimitiveIntegerOperations.mid(x,y,z); assertTrue(result ==
         * (Integer)model.get("y").getValue()); }
         */

    }

    @Test
    public void testMidTwoExternal() throws Exception {

        setup("midTwoExternal");

        // printSymbolicExecutionTreePathConditions(
        // environment.getBuilder().getStartNode());

        ArrayList<IExecutionNode> nodes =
                retrieveNode(environment.getBuilder().getStartNode(), "mid=y");

        for (IExecutionNode node : nodes) {

            System.out.println("MidTwoExternal:");
            printSingleNode(node);
        }

        /*
         * System.out.println(modelGenerator.generateNodeModel(node,
         * node.getServices())); HashMap<String, ValueContainer> model =
         * parseZ3Model(modelGenerator.generateNodeModel(node,
         * node.getServices())); printModel(model); int x =
         * (Integer)model.get("x").getValue(); int y =
         * (Integer)model.get("y").getValue(); int z =
         * (Integer)model.get("z").getValue(); int result =
         * PrimitiveIntegerOperations.mid(x,y,z); assertTrue(result ==
         * (Integer)model.get("y").getValue()); }
         */

    }

    @Test
    public void testMidOneExternal() throws Exception {

        setup("midOneExternal");

        // printSymbolicExecutionTreePathConditions(
        // environment.getBuilder().getStartNode());

        ArrayList<IExecutionNode> nodes =
                retrieveNode(environment.getBuilder().getStartNode(), "mid=y");

        for (IExecutionNode node : nodes) {

            System.out.println("MidOneExternal:");
            printSingleNode(node);
        }

        /*
         * System.out.println(modelGenerator.generateNodeModel(node,
         * node.getServices())); HashMap<String, ValueContainer> model =
         * parseZ3Model(modelGenerator.generateNodeModel(node,
         * node.getServices())); printModel(model); int x =
         * (Integer)model.get("x").getValue(); int y =
         * (Integer)model.get("y").getValue(); int z =
         * (Integer)model.get("z").getValue(); int result =
         * PrimitiveIntegerOperations.mid(x,y,z); assertTrue(result ==
         * (Integer)model.get("y").getValue()); }
         */

    }

    @Test
    public void testEasterDate()
            throws FileNotFoundException, ProofInputException,
            ModelGeneratorException {

        /*
         * No idea why this is broken, but broken it is. setup("easterDate");
         */
    }

    @Test
    public void testEuclides()
            throws FileNotFoundException, ProofInputException,
            ModelGeneratorException {

        /*
         * For recursion to work, we will need a different strategy setting. How
         * we can infer what strategy to be used, is not clear at this stage.
         * setup("euclides");
         */
    }

    /**
     * Tests that we are able to generate path conditions in such a way that all
     * possible return values for each input variable to mid() are taken.
     * 
     * @throws Exception
     */
    @Test
    public void testMid() throws Exception {

        setup("mid");

        testMidReturn("x");
        testMidReturn("y");
        testMidReturn("z");
    }

    /**
     * Test various return values for the mid method.
     * 
     * @param variable
     *            - can be x, y or z. See signature for mid.
     * @throws Exception
     */
    private void testMidReturn(String variable) throws Exception {

        ArrayList<IExecutionNode> nodes =
                retrieveNode(environment.getBuilder().getStartNode(), "mid="
                        + variable);

        /*
         * For each node, generate a model for it, refine that model, and then
         * use the resulting fixture in order to run the method under test and
         * assert correct results.
         */
        for (IExecutionNode node : nodes) {

            System.out.println("Mid " + variable);
            printSingleNode(node);

            IModel model = modelGenerator.generateModel(node);

            Map<String, IModelVariable> variableMapping =
                    model.getVariableNameMapping();

            int x = (Integer) variableMapping.get("x").getValue();
            int y = (Integer) variableMapping.get("y").getValue();
            int z = (Integer) variableMapping.get("z").getValue();
            int result = PrimitiveIntegerOperations.mid(x, y, z);

            System.out.println("Satisfiable assignment: x=" + x + " y=" + y
                    + " z=" + z);

            assertTrue(result == (Integer) variableMapping.get(variable)
                    .getValue());
        }
    }

    private void setup(String method)
            throws ProofInputException, ModelGeneratorException, IOException {

        if (modelGenerator == null) {
            modelGenerator = ModelGenerator.getDefaultModelGenerator();
        }

        environment =
                getPreparedEnvironment(
                        keyRepDirectory, javaPathInBaseDir, containerTypeName,
                        method, null, false);
    }
}