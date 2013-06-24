package se.gu.svanefalk.testgeneration.core.model;

import java.io.IOException;
import java.util.List;

import junit.framework.Assert;

import org.junit.Test;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

import se.gu.svanefalk.testgeneration.core.CoreTest;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.core.model.implementation.Model;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelGenerator;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelVariable;

public class ModelIntegerTest extends CoreTest {

    private final ModelGenerator modelGenerator = ModelGenerator.getInstance();

    public ModelIntegerTest() throws KeYInterfaceException, IOException {
        super();
    }

    @Test
    public void testSolveSingleLessThanConstraintMin() throws ProofInputException,
            ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("min");
        List<IExecutionNode> nodes = retrieveNode(methodTree, "return a");
        Assert.assertTrue(nodes.size() == 1);

        IExecutionNode targetNode = nodes.get(0);
        Model model = modelGenerator.generateModel(targetNode);

        ModelVariable variableSelf = model.getVariable("self");
        Assert.assertNotNull(variableSelf);

        // Check variable a
        ModelVariable variableA = model.getVariable("a");
        Assert.assertNotNull(variableA);
        Assert.assertTrue(variableA.getValue() instanceof Integer);
        Integer valueA = variableA.getValue();
        Assert.assertNotNull(valueA);

        // Check variable b
        ModelVariable variableB = model.getVariable("b");
        Assert.assertNotNull(variableB);
        Assert.assertTrue(variableB.getValue() instanceof Integer);
        Integer valueB = variableB.getValue();
        Assert.assertNotNull(valueB);

        System.out.println(targetNode.getFormatedPathCondition());
        System.out.println(valueA);
        System.out.println(valueB);
        // Check that the constraint holds
        Assert.assertTrue(valueA < valueB);
    }
    
    @Test
    public void testSolveSingleLessThanConstraintMax() throws ProofInputException,
            ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("max");
        List<IExecutionNode> nodes = retrieveNode(methodTree, "return b");
        Assert.assertTrue(nodes.size() == 1);

        IExecutionNode targetNode = nodes.get(0);
        Model model = modelGenerator.generateModel(targetNode);

        ModelVariable variableSelf = model.getVariable("self");
        Assert.assertNotNull(variableSelf);

        // Check variable a
        ModelVariable variableA = model.getVariable("a");
        Assert.assertNotNull(variableA);
        Assert.assertTrue(variableA.getValue() instanceof Integer);
        Integer valueA = variableA.getValue();
        Assert.assertNotNull(valueA);

        // Check variable b
        ModelVariable variableB = model.getVariable("b");
        Assert.assertNotNull(variableB);
        Assert.assertTrue(variableB.getValue() instanceof Integer);
        Integer valueB = variableB.getValue();
        Assert.assertNotNull(valueB);

        System.out.println(targetNode.getFormatedPathCondition());
        System.out.println(valueA);
        System.out.println(valueB);
        // Check that the constraint holds
        Assert.assertTrue(valueA <= valueB);
    }

    @Test
    public void testSolveSingleGreaterThanConstraintMax()
            throws ProofInputException, ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("max");
        List<IExecutionNode> nodes = retrieveNode(methodTree, "return a");
        Assert.assertTrue(nodes.size() == 1);

        IExecutionNode targetNode = nodes.get(0);
        Model model = modelGenerator.generateModel(targetNode);

        ModelVariable variableSelf = model.getVariable("self");
        Assert.assertNotNull(variableSelf);

        // Check variable a
        ModelVariable variableA = model.getVariable("a");
        Assert.assertNotNull(variableA);
        Assert.assertTrue(variableA.getValue() instanceof Integer);
        Integer valueA = variableA.getValue();
        Assert.assertNotNull(valueA);

        // Check variable b
        ModelVariable variableB = model.getVariable("b");
        Assert.assertNotNull(variableB);
        Assert.assertTrue(variableB.getValue() instanceof Integer);
        Integer valueB = variableB.getValue();
        Assert.assertNotNull(valueB);

        System.out.println(targetNode.getFormatedPathCondition());
        System.out.println(valueA);
        System.out.println(valueB);
        // Check that the constraint holds
        Assert.assertTrue(valueA > valueB);
    }
    
   

    @Test
    public void testSolveSingleGreaterThanConstraintMin()
            throws ProofInputException, ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("min");
        List<IExecutionNode> nodes = retrieveNode(methodTree, "return b");
        Assert.assertTrue(nodes.size() == 1);

        IExecutionNode targetNode = nodes.get(0);
        Model model = modelGenerator.generateModel(targetNode);

        ModelVariable variableSelf = model.getVariable("self");
        Assert.assertNotNull(variableSelf);

        // Check variable a
        ModelVariable variableA = model.getVariable("a");
        Assert.assertNotNull(variableA);
        Assert.assertTrue(variableA.getValue() instanceof Integer);
        Integer valueA = variableA.getValue();
        Assert.assertNotNull(valueA);

        // Check variable b
        ModelVariable variableB = model.getVariable("b");
        Assert.assertNotNull(variableB);
        Assert.assertTrue(variableB.getValue() instanceof Integer);
        Integer valueB = variableB.getValue();
        Assert.assertNotNull(valueB);

        System.out.println(targetNode.getFormatedPathCondition());
        System.out.println(valueA);
        System.out.println(valueB);
        // Check that the constraint holds
        Assert.assertTrue(valueA >= valueB);
    }
}
