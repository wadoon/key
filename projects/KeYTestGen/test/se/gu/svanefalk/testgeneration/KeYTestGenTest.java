package se.gu.svanefalk.testgeneration;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;

import junit.framework.Assert;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * This class provides the basic functionality needed in order to construct test
 * cases for KeYTestGen.
 * 
 * @author Christopher Svanefalk
 */
public abstract class KeYTestGenTest extends AbstractSymbolicExecutionTestCase {

    protected static class SMTSettings implements
            de.uka.ilkd.key.smt.SMTSettings {

        @Override
        public boolean checkForSupport() {

            return false;

        }

        @Override
        public String getLogic() {

            return "AUFLIA";
        }

        @Override
        public int getMaxConcurrentProcesses() {

            return 1;
        }

        @Override
        public long getMaximumInteger() {

            return ProofDependentSMTSettings.getDefaultSettingsData().maxInteger;
        }

        @Override
        public int getMaxNumberOfGenerics() {

            return 2;
        }

        @Override
        public long getMinimumInteger() {

            return ProofDependentSMTSettings.getDefaultSettingsData().minInteger;
        }

        @Override
        public String getSMTTemporaryFolder() {

            return PathConfig.getKeyConfigDir() + File.separator
                    + "smt_formula";
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
        public boolean useAssumptionsForBigSmallIntegers() {

            return false;
        }

        @Override
        public boolean useBuiltInUniqueness() {

            return false;
        }

        @Override
        public boolean useExplicitTypeHierarchy() {

            return false;
        }

        @Override
        public boolean useUninterpretedMultiplicationIfNecessary() {

            return false;
        }
    }

    protected IExecutionMethodCall getMethodCallNode(
            final IExecutionStartNode root) {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(
                root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            if (next instanceof IExecutionMethodCall) {
                return (IExecutionMethodCall) next;
            }
        }
        return null;
    }

    /**
     * Creates a {@link SymbolicExecutionEnvironment} which consists of loading
     * a file to load, finding the method to proof, instantiation of proof and
     * creation with configuration of {@link SymbolicExecutionTreeBuilder}.
     * 
     * @param baseDir
     *            The base directory which contains test and oracle file.
     * @param javaPathInBaseDir
     *            The path to the java file inside the base directory.
     * @param containerTypeName
     *            The name of the type which contains the method.
     * @param methodFullName
     *            The method name to search.
     * @param precondition
     *            An optional precondition to use.
     * @param mergeBranchConditions
     *            Merge branch conditions?
     * @return The created {@link SymbolicExecutionEnvironment}.
     * @throws ProofInputException
     *             Occurred Exception.
     * @author Martin Hentschel (mods by Christopher)
     * @throws IOException
     * @throws ProblemLoaderException
     */
    protected SymbolicExecutionEnvironment<CustomConsoleUserInterface> getPreparedEnvironment(
            final File keyRepo, final String rootFolder,
            final String resourceFile, final String method,
            final String precondition, final boolean mergeBranchConditions)
            throws ProofInputException, IOException, ProblemLoaderException {

        final SymbolicExecutionEnvironment<CustomConsoleUserInterface> env = AbstractSymbolicExecutionTestCase.createSymbolicExecutionEnvironment(
                AbstractSymbolicExecutionTestCase.keyRepDirectory, rootFolder,
                resourceFile, method, null, false, false, false);

        Assert.assertNotNull(env);

        final Proof proof = env.getProof();

        final ExecutedSymbolicExecutionTreeNodesStopCondition stopCondition = new ExecutedSymbolicExecutionTreeNodesStopCondition(
                ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN);

        proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(
                stopCondition);

        env.getUi().startAndWaitForAutoMode(proof);

        env.getBuilder().analyse();

        return env;
    }

    protected void printBranchNodes(final IExecutionStartNode root)
            throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(
                root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            if (next instanceof IExecutionBranchNode) {
                System.out.println(((IExecutionBranchNode) next).getActivePositionInfo());
                System.out.println(((IExecutionBranchNode) next).getActiveStatement());
                printSingleNode(next);
            }
        }
    }

    protected void printExecutionReturnStatementNodes(
            final IExecutionStartNode root) throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(
                root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            if (next instanceof ExecutionMethodReturn) {
                printSingleNode(next);
            }
        }
    }

    protected void printExecutionStatementNodes(final IExecutionStartNode root)
            throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(
                root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            if (next instanceof IExecutionStatement) {
                printSingleNode(next);
            }
        }
    }

    protected void printExecutionStateNodes(final IExecutionStartNode root)
            throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(
                root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            if (next instanceof IExecutionStateNode<?>) {
                printSingleNode(next);
                final IExecutionStateNode<SourceElement> stuff = (IExecutionStateNode<SourceElement>) next;
                for (final IExecutionVariable var : SymbolicExecutionUtil.createExecutionVariables(stuff)) {
                    System.out.println("\n" + var.getProgramVariable());
                    for (final IExecutionValue val : var.getValues()) {

                        System.out.println("\t" + val.getValueString());
                        System.out.println("\t" + val.getTypeString());
                    }
                }
            }
        }
    }

    protected void printJavaInfo(final IExecutionStartNode root) {

        final JavaInfo info = root.getMediator().getJavaInfo();

        for (final KeYJavaType type : info.getAllKeYJavaTypes()) {
            System.out.println(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS);

        }
    }

    protected void printNamespaceProgramVariables(
            final SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment) {

        final int i = 0;
        Namespace namespace = environment.getInitConfig().progVarNS();

        while (namespace != null) {

            System.out.println("**Namespace level: " + i + "**");
            for (final Named named : namespace.elements()) {
                System.out.println(named);
            }

            namespace = namespace.parent();
        }
    }

    protected void printNamespaceVariables(
            final SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment) {

        final int i = 0;
        Namespace namespace = environment.getInitConfig().varNS();

        while (namespace != null) {

            System.out.println("**Namespace level: " + i + "**");
            for (final Named named : namespace.elements()) {
                System.out.println(named);
            }

            namespace = namespace.parent();
        }
    }

    protected void printSingleNode(final IExecutionNode node)
            throws ProofInputException {

        System.out.println("\nNode " + node.getName() + "\nType: "
                + node.getClass() + "\nPath condition "
                + node.getPathCondition() + "\nHuman readable: "
                + node.getFormatedPathCondition().replaceAll("\n|\t", "")
                + "\nAddress: " + node.hashCode());

        System.out.println("Children:");
        for (final IExecutionNode child : node.getChildren()) {
            System.out.println("\t" + child.getName());
            System.out.println("\t" + child.getClass());
            System.out.println("\t" + child.getFormatedPathCondition());
        }
    }

    protected void printSymbolicExecutionTree(final IExecutionStartNode root)
            throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(
                root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            printSingleNode(next);
        }
    }

    protected void printSymbolicExecutionTreePathConditions(
            final IExecutionStartNode root) throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(
                root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            if (next instanceof IExecutionStateNode<?>) {

                final IExecutionStateNode<?> stateNode = (IExecutionStateNode<?>) next;
                System.out.println("Node "
                        + stateNode.getName()
                        + "\nPath condition "
                        + stateNode.getPathCondition()
                        + "\nHuman readable: "
                        + stateNode.getFormatedPathCondition().replaceAll(
                                "\n|\t", "") + "\n");
            }
        }
    }

    protected void printTermAST(final Term term) {

        System.out.println("\nTerm: " + term + "\nhas runtime class: "
                + term.getClass() + "\nand sort: "
                + term.sort().declarationString() + "\n\twith runtime type: "
                + term.sort().getClass() + "\nand op: " + term.op()
                + "\n\twith runtime type: " + term.op().getClass() + "\n"
                + "Number of subs: " + term.arity() + "\n");

        for (int i = 0; i < term.arity(); i++) {

            for (final QuantifiableVariable variable : term.varsBoundHere(i)) {
                System.out.println(term + " has bound variable: " + variable);
            }
        }

        for (int i = 0; i < term.arity(); i++) {
            System.out.println("Printing child " + i + " of current node");
            printTermAST(term.sub(i));
        }
    }

    protected void printVars(final Term term) {

        if (term.op() instanceof LocationVariable) {
            System.out.println(term);
        }

        for (int i = 0; i < term.arity(); i++) {
            printVars(term.sub(i));
        }

    }

    /**
     * Retrieve all nodes corresponding to a given program statement.
     * 
     * @param rootNode
     *            starting node for the symbolic execution tree
     * @param statement
     *            the statement to search for
     * @return
     * @throws ProofInputException
     */
    protected ArrayList<IExecutionNode> retrieveNode(
            final IExecutionStartNode rootNode, final String statement)
            throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(
                rootNode);

        final ArrayList<IExecutionNode> nodes = new ArrayList<IExecutionNode>();

        while (iterator.hasNext()) {
            final IExecutionNode next = iterator.next();
            if (next.getName().trim().equalsIgnoreCase(statement + ";")) {
                nodes.add(next);
            }
        }

        return nodes;
    }
}