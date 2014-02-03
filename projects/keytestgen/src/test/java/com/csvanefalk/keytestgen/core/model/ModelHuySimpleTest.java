package com.csvanefalk.keytestgen.core.model;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.core.model.implementation.Model;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import org.junit.Assert;
import org.junit.Test;

import java.io.IOException;

/**
 * Test cases provided by Do Huy at Darmstadt.
 */
public class ModelHuySimpleTest extends ModelTest {

    public ModelHuySimpleTest() throws KeYInterfaceException, IOException {
        super("own", false, "Simple.java");
    }

    @Test
    public void testIf() throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("Simple.magic",
                                                               "this.l=this.l+1");

        Model model = modelGenerator.generateModel(node);

        int self_h = model.getVariable("self_h").getValue();
        Assert.assertTrue(self_h > 0);
    }

    @Test
    public void testElse() throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("Simple.magic",
                                                               "this.l=this.l+2");

        Model model = modelGenerator.generateModel(node);

        int self_h = model.getVariable("self_h").getValue();
        Assert.assertTrue(self_h <= 0);
    }

    @Test
    public void testIf2() throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("Simple.magic2",
                                                               "l=l+1");

        Model model = modelGenerator.generateModel(node);

        int self_h = model.getVariable("h").getValue();
        Assert.assertTrue(self_h > 0);
    }

    @Test
    public void testElse2() throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("Simple.magic2",
                                                               "l=l+h");

        Model model = modelGenerator.generateModel(node);

        int self_h = model.getVariable("h").getValue();
        Assert.assertTrue(self_h <= 0);
    }

    @Test
    public void testIf3() throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("Simple.magic3",
                                                               "l=l+1");

        Model model = modelGenerator.generateModel(node);

        int self_h = model.getVariable("h").getValue();
        Assert.assertTrue(self_h <= 0);
    }

    @Test
    public void testElse3() throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("Simple.magic3",
                                                               "l=l+h");

        Model model = modelGenerator.generateModel(node);

        int self_h = model.getVariable("h").getValue();
        Assert.assertTrue(self_h > 0);
    }
}