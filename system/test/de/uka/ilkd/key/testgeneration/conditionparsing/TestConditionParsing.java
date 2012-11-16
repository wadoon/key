package de.uka.ilkd.key.testgeneration.conditionparsing;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.op.TermTransformer;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.proof.DefaultProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.KeYTestGenTest;
import de.uka.ilkd.key.testgeneration.TestGeneratorException;
import de.uka.ilkd.key.testgeneration.model.IModelGenerator;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelGenerator;
import de.uka.ilkd.key.testgeneration.parsers.PathconditionParser;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class TestConditionParsing
        extends KeYTestGenTest {

    private final String javaPathInBaseDir =
            "system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java";
    private final String containerTypeName = "PrimitiveIntegerOperations";

    private boolean debug = true;

    @Before
    public void setUp() throws Exception {

    }

    @Test
    public void testSimpleBuilderExtraction()
            throws ProofInputException, TestGeneratorException, IOException {

        SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment =
                createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInBaseDir,
                        containerTypeName, "max", null, false);

        Proof proof = environment.getProof();

        ExecutedSymbolicExecutionTreeNodesStopCondition stopCondition =
                new ExecutedSymbolicExecutionTreeNodesStopCondition(ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN);

        proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(
                stopCondition);

        environment.getUi().startAndWaitForProof(proof);

        environment.getBuilder().analyse();

        printSymbolicExecutionTree(environment.getBuilder().getStartNode());
    }

    @Test
    public void testProofNodeExtraction()
            throws ProofInputException, ModelGeneratorException, IOException {

        String method = "max";
        SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment =
                getEnvironmentForMethod(method);

        IExecutionStartNode start = environment.getBuilder().getStartNode();
        // IExecutionNode targetNode = retrieveNode(start, "return max").get(0);

        System.out.println(environment.getBuilder().getProof());
    }

    @Test
    public void testASTProcessing()
            throws ProofInputException, ModelGeneratorException, IOException {

        String method = "maxProxyInstance";
        SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment =
                getEnvironmentForMethod(method);

        IExecutionStartNode start = environment.getBuilder().getStartNode();
        IExecutionNode targetNode = retrieveNode(start, "return x").get(0);
        Term targetNodeCondition = targetNode.getPathCondition();

        // printDebug(method, targetNode);

        PathconditionParser parser = new PathconditionParser();
        System.out.println(parser.simplifyTerm(targetNodeCondition));
    }

    private SymbolicExecutionEnvironment<CustomConsoleUserInterface> getEnvironmentForMethod(
            String method)
            throws ProofInputException, ModelGeneratorException, IOException {

        return getPreparedEnvironment(keyRepDirectory, javaPathInBaseDir,
                containerTypeName, method, null, false);
    }

    private void printDebug(String method, IExecutionNode node)
            throws ProofInputException {

        if (!debug) {
            return;
        }

        System.out.println("\n\n************" + method + "************\n");
        printSingleNode(node);
        printTermAST(node.getPathCondition());
        // printVars(term);

    }

    private List<Term> extractVariables(Term term) {

        LinkedList<Term> toReturn = new LinkedList<Term>();
        LinkedList<Term> toVisit = new LinkedList<Term>();
        toVisit.add(term);
        while (!toVisit.isEmpty()) {

            Term currentTerm = toVisit.poll();

            /*
             * Queue child elements of the current term for visition
             */
            for (Term nextTerm : term.subs()) {
                toReturn.add(nextTerm);
            }
        }

        return null;
    }

    protected void printInstance(Term term) {

        if (term.op() instanceof SortedOperator) {
            System.out.println("\nTerm: " + term + "\nhas runtime class: "
                    + term.getClass() + "\nand sort: " + term.sort().declarationString()
                    + "\n\twith runtime type: " + term.sort().getClass() + "\nand op: "
                    + term.op() + "\n\twith runtime type: " + term.op().getClass() + "\n"
                    + "Number of subs");
        }

        for (int i = 0; i < term.arity(); i++) {
            printInstance(term.sub(i));
        }
    }

}
