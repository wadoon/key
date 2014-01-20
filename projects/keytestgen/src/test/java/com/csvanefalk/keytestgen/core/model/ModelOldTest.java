package com.csvanefalk.keytestgen.core.model;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.core.model.implementation.Model;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import org.junit.Assert;
import org.junit.Test;

import java.io.IOException;

public class ModelOldTest extends ModelTest {

    public ModelOldTest() throws KeYInterfaceException, IOException {
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
}