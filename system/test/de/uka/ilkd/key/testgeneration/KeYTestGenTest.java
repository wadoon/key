package de.uka.ilkd.key.testgeneration;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map.Entry;
import java.util.StringTokenizer;




import com.sun.org.apache.xpath.internal.operations.Bool;

import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.parser.proofjava.ParseException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.testgeneration.parser.z3parser.api.Z3ModelParser;
import de.uka.ilkd.key.testgeneration.parser.z3parser.api.Z3Visitor.ValueContainer;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * This class provides the basic functionality needed in order to construct 
 * test cases for KeYTestGen.
 * 
 * @author Christopher Svanefalk
 */
public class KeYTestGenTest extends AbstractSymbolicExecutionTestCase {

    /**
     * Creates a {@link SymbolicExecutionEnvironment} which consists
     * of loading a file to load, finding the method to proof, instantiation
     * of proof and creation with configuration of {@link SymbolicExecutionTreeBuilder}.
     * @param baseDir The base directory which contains test and oracle file.
     * @param javaPathInBaseDir The path to the java file inside the base directory.
     * @param containerTypeName The name of the type which contains the method.
     * @param methodFullName The method name to search.
     * @param precondition An optional precondition to use.
     * @param mergeBranchConditions Merge branch conditions?
     * @return The created {@link SymbolicExecutionEnvironment}.
     * @throws ProofInputException Occurred Exception.
     * @author Martin Hentschel (mods by Christopher)
     * @throws IOException 
     */
     protected SymbolicExecutionEnvironment<CustomConsoleUserInterface> getPreparedEnvironment(
            File keyRepo,
            String rootFolder,
            String resourceFile,
            String method,
            String precondition,
            boolean mergeBranchConditions) throws ProofInputException, IOException {

        SymbolicExecutionEnvironment<CustomConsoleUserInterface> env = 
                createSymbolicExecutionEnvironment(keyRepDirectory, 
                        rootFolder, 
                        resourceFile, 
                        method,
                        null, 
                        false
                        );
        
        assertNotNull(env);

        Proof proof = env.getProof();

        ExecutedSymbolicExecutionTreeNodesStopCondition stopCondition = 
                new ExecutedSymbolicExecutionTreeNodesStopCondition(
                        ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN);

        proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);

        env.getUi().startAndWaitForProof(proof);

        env.getBuilder().analyse();



        return env;
    }

    /**
     * Return all nodes in the execution tree where a given statement occurs.
     * 
     * @param nodeName
     * @return
     * @throws ProofInputException
     * 
     *  @author christopher
     */
    protected ArrayList<IExecutionNode> retrieveNode(IExecutionStartNode rootNode, String statement)
            throws ProofInputException {

        ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(rootNode);
        ArrayList<IExecutionNode> nodes = new ArrayList<IExecutionNode>();

        while (iterator.hasNext()) {
            IExecutionNode next = iterator.next();

            if(next.getName().trim().equalsIgnoreCase(statement + ";")) {
                nodes.add(next);
            }
        }

        return nodes;
    }

    protected void printSymbolicExecutionTree(IExecutionStartNode root) throws ProofInputException {

        ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(root);

        while (iterator.hasNext()) {

            IExecutionNode next = iterator.next();

            if (next instanceof IExecutionStateNode<?>){
                IExecutionStateNode<?> stateNode = (IExecutionStateNode<?>)next;

                System.out.println(stateNode.getName());   
            }
        } 
    }

    protected void printModel(HashMap<String, ValueContainer> model) {

        for(ValueContainer container : model.values()) {

            System.out.println("GENERATED MODEL:" + 
                    "\nName: " + container.getName() + 
                    "\nType: " + container.getType() + 
                    "\nValue: " + container.getValue() +
                    "\n");
        }
    }

    protected void printSymbolicExecutionTreePathConditions(IExecutionStartNode root) throws ProofInputException {

        ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(root);

        while (iterator.hasNext()) {

            IExecutionNode next = iterator.next();

            if (next instanceof IExecutionStateNode<?>){

                IExecutionStateNode<?> stateNode = (IExecutionStateNode<?>)next;
                System.out.println("Node " + stateNode.getName() + 
                        "\nPath condition " + stateNode.getPathCondition() +
                        "\nHuman readable: " + stateNode.getFormatedPathCondition().replaceAll("\n|\t", "") +
                        "\n");   
            }
        }
    }

    protected void printSingleNode(IExecutionNode node) throws ProofInputException {

        System.out.println("Node " + node.getName() + 
                "\nPath condition " + node.getPathCondition() +
                "\nHuman readable: " + node.getFormatedPathCondition().replaceAll("\n|\t", "") +
                "\n");   
    }


    protected static class SMTSettings implements de.uka.ilkd.key.smt.SMTSettings{

        @Override
        public int getMaxConcurrentProcesses() {
            return 1;
        }

        @Override
        public int getMaxNumberOfGenerics() {
            return 2;
        }

        @Override
        public String getSMTTemporaryFolder() {
            return   PathConfig.getKeyConfigDir()
                    + File.separator + "smt_formula";
        }

        @Override
        public Collection<Taclet> getTaclets() {
            return null;
        }

        @Override
        public long getTimeout() {
            return 5000;
        }

        @Override
        public boolean instantiateNullAssumption() {
            return true;
        }

        @Override
        public boolean makesUseOfTaclets() {
            return false;
        }

        @Override
        public boolean useExplicitTypeHierarchy() {
            return false;
        }

        @Override
        public boolean useBuiltInUniqueness() {
            return false;
        }

        @Override
        public boolean useAssumptionsForBigSmallIntegers() {
            return false;
        }

        @Override
        public boolean useUninterpretedMultiplicationIfNecessary() {
            return false;
        }

        @Override
        public long getMaximumInteger() {

            return ProofDependentSMTSettings.getDefaultSettingsData().maxInteger;
        }

        @Override
        public long getMinimumInteger() {

            return ProofDependentSMTSettings.getDefaultSettingsData().minInteger;
        }

        @Override
        public String getLogic() {
            return "AUFLIA";
        }

        @Override
        public boolean checkForSupport() {
            return false;

        }
    }
}