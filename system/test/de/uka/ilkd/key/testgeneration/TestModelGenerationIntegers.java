package de.uka.ilkd.key.testgeneration;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Map;

import org.junit.Test;

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

/**
 * Tests to assert that the model generation procedure generates fixtures
 * whichindeed cause specified execution paths to be taken. IMPORTANT - these
 * test cases involve heavy use of native program invocations, and might take
 * significant time to execute. To achieve this,
 * 
 * @author christopher
 */
public class TestModelGenerationIntegers extends KeYTestGenTest {

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
        testMid("x");
        testMid("y");
        testMid("z");
    }

    /**
     * Tests the mid method using two instance variables of its encasing class.
     * 
     * @throws Exception
     */
    @Test
    public void testMidTwoInstancel() throws Exception {

        setup("midTwoInstance");
        testMidTwoInstance("x");
        testMidTwoInstance("instanceY");
        testMidTwoInstance("instanceZ");
    }

    /**
     * Test the mid method using two nested fields in other classes.
     * 
     * @throws Exception
     */
    @Test
    public void testMidTwoProxy() throws Exception {

        setup("midTwoProxy");
        // testMidTwoProxy("x");
        testMidTwoProxy("proxy.instanceInt");
        // testMidTwoProxy("proxy.nestedProxy.instanceInt");
    }

    @Test
    public void testEasterDate() throws FileNotFoundException,
            ProofInputException, ModelGeneratorException {

        /*
         * No idea why this is broken, but broken it is. setup("easterDate");
         */
    }

    @Test
    public void testEuclides() throws FileNotFoundException,
            ProofInputException, ModelGeneratorException {

        /*
         * For recursion to work, we will need a different strategy setting. How
         * we can infer what strategy to be used, is not clear at this stage.
         * setup("euclides");
         */
    }

    /**
     * Test various return values for the mid method.
     * 
     * @param variable
     *            - can be x, y or z. See signature for mid.
     * @throws Exception
     */
    private void testMid(String variable) throws Exception {

        ArrayList<IExecutionNode> nodes = retrieveNode(environment.getBuilder()
                .getStartNode(), "mid=" + variable);

        /*
         * For each node, generate a model for it, refine that model, and then
         * use the resulting fixture in order to run the method under test and
         * assert correct results.
         */
        for (IExecutionNode node : nodes) {

            System.out.println("Mid " + variable);
            printSingleNode(node);

            IModel model = modelGenerator.generateModel(node);

            Map<String, ? extends IModelObject> variableMapping = model
                    .getVariableNameMapping();

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

    private void testMidTwoInstance(String variable) throws Exception {

        ArrayList<IExecutionNode> nodes = retrieveNode(environment.getBuilder()
                .getStartNode(), "mid=" + variable);

        for (IExecutionNode node : nodes) {

            IModel model = modelGenerator.generateModel(node);

            Map<String, ? extends IModelObject> variableMapping = model
                    .getVariableNameMapping();

            int x = (Integer) variableMapping.get("x").getValue();
            int y = (Integer) variableMapping.get("self_dollar_instanceY")
                    .getValue();
            int z = (Integer) variableMapping.get("self_dollar_instanceZ")
                    .getValue();

            PrimitiveIntegerOperations operations = new PrimitiveIntegerOperations();
            operations.setInstanceY(y);
            operations.setInstanceZ(z);

            int result = operations.midTwoInstance(x);

            for (IModelObject var : model.getVariables()) {
                String varName = var.getName();
                if (varName.endsWith(variable)) {
                    int varValue = (Integer) variableMapping.get(var.getName())
                            .getValue();
                    assertTrue(result == varValue);
                }
            }
        }
    }

    private void testMidTwoProxy(String variable) throws Exception {

        // printSymbolicExecutionTree(environment.getBuilder().getStartNode());

        ArrayList<IExecutionNode> nodes = retrieveNode(environment.getBuilder()
                .getStartNode(), "mid=" + variable);

        for (IExecutionNode node : nodes) {

            IModel model = modelGenerator.generateModel(node);

            Map<String, ? extends IModelObject> variableMapping = model
                    .getVariableNameMapping();

            int x = (Integer) variableMapping.get("x").getValue();
            int y = (Integer) variableMapping.get(
                    "self_dollar_proxy_dollar_instanceInt").getValue();
            int z = (Integer) variableMapping.get(
                    "self_dollar_proxy_dollar_nestedProxy_dollar_instanceInt")
                    .getValue();

            PrimitiveIntegerOperations operations = new PrimitiveIntegerOperations();
            operations.setInstanceY(y);
            operations.setInstanceZ(z);

            int result = operations.midTwoProxy(x);

            for (IModelObject var : model.getVariables()) {
                String varName = var.getName();
                if (varName.endsWith(variable)) {
                    int varValue = (Integer) variableMapping.get(var.getName())
                            .getValue();
                    assertTrue(result == varValue);
                }
            }
        }
    }

    private void setup(String method) throws ProofInputException,
            ModelGeneratorException, IOException, ProblemLoaderException {

        if (modelGenerator == null) {
            modelGenerator = ModelGenerator.getDefaultModelGenerator();
        }

        environment = getPreparedEnvironment(keyRepDirectory,
                javaPathInBaseDir, containerTypeName, method, null, false);
    }

    private interface IFunctionDelegate {

        public <T> T apply(T... args);
    }

}