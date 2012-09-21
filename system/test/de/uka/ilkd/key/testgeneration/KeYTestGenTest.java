package de.uka.ilkd.key.testgeneration;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.StringTokenizer;

import z3parser.api.Z3ModelParser;
import z3parser.api.Z3ModelParser.ValueContainer;
import z3parser.parser.Yylex;
import z3parser.parser.parser;
import z3parser.tree.Model;


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
    /*
    protected SymbolicExecutionEnvironment<CustomConsoleUserInterface> getSymbolicExecutionEnvironment (
            File baseDir, 
            String javaPathInBaseDir, 
            String containerTypeName, 
            String methodFullName,
            String precondition,
            boolean mergeBranchConditions) throws ProofInputException, FileNotFoundException {


        // Make sure that required files exists
        File javaFile = new File(baseDir, javaPathInBaseDir);
        assertTrue(javaFile.exists());

        // Create user interface
        CustomConsoleUserInterface ui = new CustomConsoleUserInterface(false);

        // Load java file
        InitConfig initConfig = ui.load(javaFile, null, null);

        // Search method to proof
        Services services = initConfig.getServices();
        IProgramMethod pm = searchProgramMethod(services, containerTypeName, methodFullName);

        // Start proof
        ProofOblInput input = new ProgramMethodPO(initConfig, pm.getFullName(), pm, precondition, true);
        Proof proof = ui.createProof(initConfig, input);
        assertNotNull(proof);

        // Set strategy and goal chooser to use for auto mode
        SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof, ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN);

        // Create symbolic execution tree which contains only the start node at beginning
        SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(ui.getMediator(), proof, mergeBranchConditions);
        builder.analyse();
        assertNotNull(builder.getStartNode());

        // Create a symbolic execution environment
        SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment = 
                new SymbolicExecutionEnvironment<CustomConsoleUserInterface>(ui, initConfig, builder);


        /*
     * Set a stop condition. For now, we will simply go with the default 
     * and simply run auto mode

        proof = environment.getProof();

        ExecutedSymbolicExecutionTreeNodesStopCondition stopCondition = 
                new ExecutedSymbolicExecutionTreeNodesStopCondition(
                        ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN);

        proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
        /*
     * Tell KeY to start running the proof
         what might save us, me and you, is if the russians love their children too

         Timeless.
        environment.getUi().startAndWaitForProof(proof);

        /*
     * Construct a symbolic execution tree for the proof

        environment.getBuilder().analyse();

        /*
     * Finally, return the environment

        return environment;

    }
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

    protected void printModel(HashMap<String, z3parser.api.Z3ModelParser.ValueContainer> model) {

        for(z3parser.api.Z3ModelParser.ValueContainer container : model.values()) {

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