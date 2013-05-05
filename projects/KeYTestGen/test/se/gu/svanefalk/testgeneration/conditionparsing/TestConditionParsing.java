package se.gu.svanefalk.testgeneration.conditionparsing;

import java.io.IOException;

import junit.framework.Assert;

import org.junit.Before;
import org.junit.Test;

import se.gu.svanefalk.testgeneration.KeYTestGenTest;
import se.gu.svanefalk.testgeneration.backend.TestGeneratorException;
import se.gu.svanefalk.testgeneration.core.model.ModelGeneratorException;
import se.gu.svanefalk.testgeneration.core.model.tools.ModelGenerationTools;
import se.gu.svanefalk.testgeneration.util.parsers.transformers.TermTransformerException;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class TestConditionParsing extends KeYTestGenTest {

    private final String containerTypeName = "PrimitiveIntegerOperations";
    private final String javaPathInBaseDir = "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> getEnvironmentForMethod(
            final String method) throws ProofInputException,
            ModelGeneratorException, IOException, ProblemLoaderException {

        return getPreparedEnvironment(
                AbstractSymbolicExecutionTestCase.keyRepDirectory,
                javaPathInBaseDir, containerTypeName, method, null, false);
    }

    protected void printInstance(final Term term) {

        if (term.op() instanceof SortedOperator) {
            System.out.println("\nTerm: " + term + "\nhas runtime class: "
                    + term.getClass() + "\nand sort: "
                    + term.sort().declarationString()
                    + "\n\twith runtime type: " + term.sort().getClass()
                    + "\nand op: " + term.op() + "\n\twith runtime type: "
                    + term.op().getClass() + "\n" + "Number of subs");
        }

        for (int i = 0; i < term.arity(); i++) {
            printInstance(term.sub(i));
        }
    }

    @Override
    @Before
    public void setUp() throws Exception {

    }

    @Test
    public void testASTProcessing() throws ProofInputException,
            ModelGeneratorException, IOException, ProblemLoaderException,
            TermTransformerException {

        final String method = "maxProxyInstance";
        final SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment = getEnvironmentForMethod(method);

        final IExecutionStartNode start = environment.getBuilder().getStartNode();
        final IExecutionNode targetNode = retrieveNode(start, "return x").get(0);
        final Term targetNodeCondition = targetNode.getPathCondition();

        final Term result = ModelGenerationTools.simplifyTerm(targetNodeCondition);
        Assert.assertFalse(result == null);
    }

    @Test
    public void testProofNodeExtraction() throws ProofInputException,
            ModelGeneratorException, IOException, ProblemLoaderException {

        final String method = "max";
        final SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment = getEnvironmentForMethod(method);

        environment.getBuilder().getStartNode();

        System.out.println(environment.getBuilder().getProof());
    }

    @Test
    public void testSimpleBuilderExtraction() throws ProofInputException,
            TestGeneratorException, IOException, ProblemLoaderException {

        final SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment = AbstractSymbolicExecutionTestCase.createSymbolicExecutionEnvironment(
                AbstractSymbolicExecutionTestCase.keyRepDirectory,
                javaPathInBaseDir, containerTypeName, "max", null, false,
                false, false);

        final Proof proof = environment.getProof();

        final ExecutedSymbolicExecutionTreeNodesStopCondition stopCondition = new ExecutedSymbolicExecutionTreeNodesStopCondition(
                ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN);

        proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(
                stopCondition);

        environment.getUi().startAndWaitForAutoMode(proof);

        environment.getBuilder().analyse();

        printSymbolicExecutionTree(environment.getBuilder().getStartNode());
    }

}
