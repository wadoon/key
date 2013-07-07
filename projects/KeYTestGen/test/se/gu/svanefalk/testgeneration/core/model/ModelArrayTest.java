package se.gu.svanefalk.testgeneration.core.model;

import java.io.IOException;

import org.junit.Ignore;
import org.junit.Test;

import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.core.model.implementation.Model;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

public class ModelArrayTest extends ModelTest {

    public ModelArrayTest() throws KeYInterfaceException, IOException {
        super("arrays");
    }

    @Test
    public void ObjectArrayIndexWriteAccess() throws ModelGeneratorException,
            ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement(
                "ObjectArrayIndexWriteAccess.compute", "return array[0].value");

        Model model = modelGenerator.generateModel(node);
    }

    @Ignore
    @Test
    public void ArrayIndexWriteAccess() throws ModelGeneratorException,
            ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement(
                "ArrayIndexWriteAccess.compute", null);
    }

    @Ignore
    @Test
    public void SimpleArrayLength() throws ModelGeneratorException,
            ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement(
                "SimpleArrayLength.compute", null);

        Model model = modelGenerator.generateModel(node);
    }

    @Ignore
    @Test
    public void ArrayInstanceCreationTest() throws ModelGeneratorException,
            ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement(
                "ArrayInstanceCreationTest.compute", null);

        Model model = modelGenerator.generateModel(node);
    }

    @Ignore
    @Test
    public void ArrayIndexReadAccess() throws ModelGeneratorException,
            ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement(
                "ArrayIndexReadAccess.compute", null);

        Model model = modelGenerator.generateModel(node);
    }

    @Ignore
    @Test
    public void VariablesArrayTest() throws ModelGeneratorException,
            ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement(
                "VariablesArrayTest.compute", null);

        Model model = modelGenerator.generateModel(node);
    }

    @Ignore
    @Test
    public void MultiArrayIndexReadWriteAccess()
            throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement(
                "MultiArrayIndexReadWriteAccess.compute", null);

        Model model = modelGenerator.generateModel(node);
    }

    @Ignore
    @Test
    public void SimpleArrayCreation() throws ModelGeneratorException,
            ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement(
                "SimpleArrayCreation.compute", null);

        Model model = modelGenerator.generateModel(node);
    }

}