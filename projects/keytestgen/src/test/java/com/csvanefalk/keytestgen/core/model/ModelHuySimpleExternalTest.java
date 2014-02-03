package com.csvanefalk.keytestgen.core.model;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.keystone.external.KeyStoneSolver;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import org.junit.Assert;
import org.junit.Test;

import java.io.IOException;
import java.util.Map;

/**
 * Test cases provided by Do Huy at Darmstadt.
 */
public class ModelHuySimpleExternalTest extends ModelTest {

    public ModelHuySimpleExternalTest() throws KeYInterfaceException, IOException {
        super("own", false, "Simple.java");
    }

    @Test
    public void testIf() throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("Simple.magic",
                                                               "this.l=this.l+1");

        KeyStoneSolver solver = new KeyStoneSolver(node.getPathCondition(), node.getServices());

        Map<String, Integer> solution = solver.solveFormula();

        int self_h = solution.get("self_h");
        Assert.assertTrue(self_h > 0);
    }

    @Test
    public void testElse() throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("Simple.magic",
                                                               "this.l=this.l+2");

        KeyStoneSolver solver = new KeyStoneSolver(node.getPathCondition(), node.getServices());

        Map<String, Integer> solution = solver.solveFormula();

        int self_h = solution.get("self_h");
        Assert.assertTrue(self_h <= 0);
    }

    @Test
    public void testIf2() throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("Simple.magic2",
                                                               "l=l+1");

        KeyStoneSolver solver = new KeyStoneSolver(node.getPathCondition(), node.getServices());

        Map<String, Integer> solution = solver.solveFormula();


        int self_h = solution.get("h");
        Assert.assertTrue(self_h > 0);
    }

    @Test
    public void testElse2() throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("Simple.magic2",
                                                               "l=l+h");

        KeyStoneSolver solver = new KeyStoneSolver(node.getPathCondition(), node.getServices());

        Map<String, Integer> solution = solver.solveFormula();


        int self_h = solution.get("h");
        Assert.assertTrue(self_h <= 0);
    }

    @Test
    public void testIf3() throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("Simple.magic3",
                                                               "l=l+1");

        KeyStoneSolver solver = new KeyStoneSolver(node.getPathCondition(), node.getServices());

        Map<String, Integer> solution = solver.solveFormula();


        int self_h = solution.get("h");
        Assert.assertTrue(self_h <= 0);
    }

    @Test
    public void testElse3() throws ModelGeneratorException, ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("Simple.magic3",
                                                               "l=l+h");

        KeyStoneSolver solver = new KeyStoneSolver(node.getPathCondition(), node.getServices());

        Map<String, Integer> solution = solver.solveFormula();

        int self_h = solution.get("h");
        Assert.assertTrue(self_h > 0);
    }
}