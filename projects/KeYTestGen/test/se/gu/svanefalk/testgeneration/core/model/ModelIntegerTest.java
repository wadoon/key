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

public class ModelIntegerTest extends ModelTest {

    public ModelIntegerTest() throws KeYInterfaceException, IOException {
        super("own");
    }

    @Test
    public void testSolveSingleLessThanConstraintMin()
            throws ProofInputException, ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("min");
        List<IExecutionNode> nodes = getSymbolicExecutionNode(methodTree,
                "return a");
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

        // Check that the constraint holds
        Assert.assertTrue(valueA < valueB);
    }

    @Test
    public void testSolveSingleLessThanConstraintMax()
            throws ProofInputException, ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("max");
        List<IExecutionNode> nodes = getSymbolicExecutionNode(methodTree,
                "return b");
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

        // Check that the constraint holds
        Assert.assertTrue(valueA <= valueB);
    }

    @Test
    public void testSolveSingleLessThanConstraintMax_2()
            throws ProofInputException, ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("max_2");
        List<IExecutionNode> nodes = getSymbolicExecutionNode(methodTree,
                "return b");
        Assert.assertTrue(nodes.size() == 1);

        IExecutionNode targetNode = nodes.get(0);
        Model model = modelGenerator.generateModel(targetNode);
        System.out.println("COND: " + targetNode.getFormatedPathCondition());
        System.out.println(targetNode.getPathCondition());

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

        // Check that the constraint holds
        Assert.assertTrue(valueA <= valueB);
    }

    @Test
    public void testSolveSingleGreaterThanConstraintMax()
            throws ProofInputException, ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("max");
        List<IExecutionNode> nodes = getSymbolicExecutionNode(methodTree,
                "return a");
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

        // Check that the constraint holds
        Assert.assertTrue(valueA > valueB);
    }

    @Test
    public void testSolveSingleGreaterThanConstraintMin()
            throws ProofInputException, ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("min");
        List<IExecutionNode> nodes = getSymbolicExecutionNode(methodTree,
                "return b");
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

        // Check that the constraint holds
        Assert.assertTrue(valueA >= valueB);
    }

    @Test
    public void testSolveCompoundConstraintMid() throws ProofInputException,
            ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("mid");
        List<IExecutionNode> nodes = getSymbolicExecutionNode(methodTree,
                "mid=y");
        Assert.assertTrue(nodes.size() == 2);

        IExecutionNode targetNode = nodes.get(0);
        Model model = modelGenerator.generateModel(targetNode);

        ModelVariable variableSelf = model.getVariable("self");
        Assert.assertNotNull(variableSelf);

        // Check variable x
        ModelVariable variableX = model.getVariable("x");
        Assert.assertNotNull(variableX);
        Assert.assertTrue(variableX.getValue() instanceof Integer);
        Integer valueX = variableX.getValue();
        Assert.assertNotNull(valueX);

        // Check variable y
        ModelVariable variableY = model.getVariable("y");
        Assert.assertNotNull(variableY);
        Assert.assertTrue(variableY.getValue() instanceof Integer);
        Integer valueY = variableY.getValue();
        Assert.assertNotNull(valueY);

        // Check variable z
        ModelVariable variableZ = model.getVariable("z");
        Assert.assertNotNull(variableZ);
        Assert.assertTrue(variableZ.getValue() instanceof Integer);
        Integer valueZ = variableZ.getValue();
        Assert.assertNotNull(valueZ);

        // Check that the constraint holds
        Assert.assertTrue(valueY < valueZ);
        Assert.assertTrue(valueX < valueY);
    }

    @Test
    public void testSolveCompoundConstraintMid2() throws ProofInputException,
            ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("mid");
        List<IExecutionNode> nodes = getSymbolicExecutionNode(methodTree,
                "mid=y");
        Assert.assertTrue(nodes.size() == 2);

        IExecutionNode targetNode = nodes.get(1);
        Model model = modelGenerator.generateModel(targetNode);

        ModelVariable variableSelf = model.getVariable("self");
        Assert.assertNotNull(variableSelf);

        // Check variable x
        ModelVariable variableX = model.getVariable("x");
        Assert.assertNotNull(variableX);
        Assert.assertTrue(variableX.getValue() instanceof Integer);
        Integer valueX = variableX.getValue();
        Assert.assertNotNull(valueX);

        // Check variable y
        ModelVariable variableY = model.getVariable("y");
        Assert.assertNotNull(variableY);
        Assert.assertTrue(variableY.getValue() instanceof Integer);
        Integer valueY = variableY.getValue();
        Assert.assertNotNull(valueY);

        // Check variable z
        ModelVariable variableZ = model.getVariable("z");
        Assert.assertNotNull(variableZ);
        Assert.assertTrue(variableZ.getValue() instanceof Integer);
        Integer valueZ = variableZ.getValue();
        Assert.assertNotNull(valueZ);

        // Check that the constraint holds
        Assert.assertFalse(valueY < valueZ);
        Assert.assertTrue(valueY < valueX);
    }

    @Test
    public void testSolveCompoundConstraintMid3() throws ProofInputException,
            ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("mid");
        List<IExecutionNode> nodes = getSymbolicExecutionNode(methodTree,
                "mid=x");
        Assert.assertTrue(nodes.size() == 2);

        IExecutionNode targetNode = nodes.get(0);
        Model model = modelGenerator.generateModel(targetNode);

        ModelVariable variableSelf = model.getVariable("self");
        Assert.assertNotNull(variableSelf);

        // Check variable x
        ModelVariable variableX = model.getVariable("x");
        Assert.assertNotNull(variableX);
        Assert.assertTrue(variableX.getValue() instanceof Integer);
        Integer valueX = variableX.getValue();
        Assert.assertNotNull(valueX);

        // Check variable y
        ModelVariable variableY = model.getVariable("y");
        Assert.assertNotNull(variableY);
        Assert.assertTrue(variableY.getValue() instanceof Integer);
        Integer valueY = variableY.getValue();
        Assert.assertNotNull(valueY);

        // Check variable z
        ModelVariable variableZ = model.getVariable("z");
        Assert.assertNotNull(variableZ);
        Assert.assertTrue(variableZ.getValue() instanceof Integer);
        Integer valueZ = variableZ.getValue();
        Assert.assertNotNull(valueZ);
        System.out.println(targetNode.getFormatedPathCondition());
        // Check that the constraint holds
        Assert.assertTrue(valueY < valueZ);
        Assert.assertTrue(valueX <= valueZ);
    }

    @Test
    public void testSolveCompoundConstraintMid4() throws ProofInputException,
            ModelGeneratorException {

        IExecutionStartNode methodTree = getSymbolicTreeForMethod("mid");
        List<IExecutionNode> nodes = getSymbolicExecutionNode(methodTree,
                "mid=x");
        Assert.assertTrue(nodes.size() == 2);

        IExecutionNode targetNode = nodes.get(1);
        Model model = modelGenerator.generateModel(targetNode);

        ModelVariable variableSelf = model.getVariable("self");
        Assert.assertNotNull(variableSelf);

        // Check variable x
        ModelVariable variableX = model.getVariable("x");
        Assert.assertNotNull(variableX);
        Assert.assertTrue(variableX.getValue() instanceof Integer);
        Integer valueX = variableX.getValue();
        Assert.assertNotNull(valueX);

        // Check variable y
        ModelVariable variableY = model.getVariable("y");
        Assert.assertNotNull(variableY);
        Assert.assertTrue(variableY.getValue() instanceof Integer);
        Integer valueY = variableY.getValue();
        Assert.assertNotNull(valueY);

        // Check variable z
        ModelVariable variableZ = model.getVariable("z");
        Assert.assertNotNull(variableZ);
        Assert.assertTrue(variableZ.getValue() instanceof Integer);
        Integer valueZ = variableZ.getValue();
        Assert.assertNotNull(valueZ);

        // Check that the constraint holds
        Assert.assertFalse(valueY < valueZ);
        Assert.assertTrue(valueY >= valueZ);
    }
}
