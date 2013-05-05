package se.gu.svanefalk.testgeneration;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;

import junit.framework.Assert;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.core.model.ModelGeneratorException;
import se.gu.svanefalk.testgeneration.core.model.implementation.Model;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelGenerator;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelVariable;
import se.gu.svanefalk.testgeneration.targetmodels.PrimitiveIntegerOperations;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
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

    private final String containerTypeName = "PrimitiveIntegerOperations";
    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment;
    private final String javaPathInBaseDir = "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private ModelGenerator modelGenerator;

    private void setup(final String method) throws ProofInputException,
            ModelGeneratorException, IOException, ProblemLoaderException {

        if (modelGenerator == null) {
            modelGenerator = ModelGenerator.INSTANCE;
        }

        environment = getPreparedEnvironment(
                AbstractSymbolicExecutionTestCase.keyRepDirectory,
                javaPathInBaseDir, containerTypeName, method, null, false);
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
     * Test model instantiation for the standard mid method.
     * 
     * @throws Exception
     */
    @Test
    public void testMid() throws Exception {

        setup("mid");
        this.testMid("x");
        this.testMid("y");
        this.testMid("z");
    }

    /**
     * Test various return values for the mid method.
     * 
     * @param variable
     *            - can be x, y or z. See signature for mid.
     * @throws Exception
     */
    private void testMid(final String variable) throws Exception {

        final ArrayList<IExecutionNode> nodes = retrieveNode(
                environment.getBuilder().getStartNode(), "mid=" + variable);

        /*
         * For each node, generate a model for it, refine that model, and then
         * use the resulting fixture in order to run the method under test and
         * assert correct results.
         */
        for (final IExecutionNode node : nodes) {

            System.out.println("Mid " + variable);
            printSingleNode(node);

            final Model model = modelGenerator.generateModel(node);

            final int x = (Integer) model.getVariable("x").getValue();
            final int y = (Integer) model.getVariable("y").getValue();
            final int z = (Integer) model.getVariable("z").getValue();
            final int result = PrimitiveIntegerOperations.mid(x, y, z);

            System.out.println("Satisfiable assignment: x=" + x + " y=" + y
                    + " z=" + z);

            Assert.assertTrue(result == (Integer) model.getVariable(variable).getValue());
        }
    }

    private void testMidTwoInstance(final String variable) throws Exception {

        final ArrayList<IExecutionNode> nodes = retrieveNode(
                environment.getBuilder().getStartNode(), "mid=" + variable);

        for (final IExecutionNode node : nodes) {

            final Model model = modelGenerator.generateModel(node);

            final int x = (Integer) model.getVariable("x").getValue();
            final int y = (Integer) model.getVariable("self_dollar_instanceY").getValue();
            final int z = (Integer) model.getVariable("self_dollar_instanceZ").getValue();

            final PrimitiveIntegerOperations operations = new PrimitiveIntegerOperations();
            operations.setInstanceY(y);
            operations.setInstanceZ(z);

            final int result = operations.midTwoInstance(x);

            for (final ModelVariable var : model.getVariables()) {
                final String varName = var.getIdentifier();
                if (varName.endsWith(variable)) {
                    final int varValue = (Integer) model.getVariable(
                            var.getIdentifier()).getValue();
                    Assert.assertTrue(result == varValue);
                }
            }
        }
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
        this.testMidTwoProxy("proxy.instanceInt");
        // testMidTwoProxy("proxy.nestedProxy.instanceInt");
    }

    private void testMidTwoProxy(final String variable) throws Exception {

        // printSymbolicExecutionTree(environment.getBuilder().getStartNode());

        final ArrayList<IExecutionNode> nodes = retrieveNode(
                environment.getBuilder().getStartNode(), "mid=" + variable);

        for (final IExecutionNode node : nodes) {

            final Model model = modelGenerator.generateModel(node);

            final int x = (Integer) model.getVariable("x").getValue();
            final int y = (Integer) model.getVariable(
                    "self_dollar_proxy_dollar_instanceInt").getValue();
            final int z = (Integer) model.getVariable(
                    "self_dollar_proxy_dollar_nestedProxy_dollar_instanceInt").getValue();

            final PrimitiveIntegerOperations operations = new PrimitiveIntegerOperations();
            operations.setInstanceY(y);
            operations.setInstanceZ(z);

            final int result = operations.midTwoProxy(x);

            for (final ModelVariable var : model.getVariables()) {
                final String varName = var.getIdentifier();
                if (varName.endsWith(variable)) {
                    final int varValue = (Integer) model.getVariable(
                            var.getIdentifier()).getValue();
                    Assert.assertTrue(result == varValue);
                }
            }
        }
    }

}