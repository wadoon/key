package com.csvanefalk.keytestgen;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.testutils.TestEnvironment;
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
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.model.*;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;
import org.junit.Assert;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * This class provides the basic functionality needed in order to construct test
 * cases for KeYTestGen.
 *
 * @author Christopher Svanefalk
 */
public abstract class KeYTestGenTest {

    private final TestEnvironment testEnvironment;

    public KeYTestGenTest(String directory) throws KeYInterfaceException, IOException {

        testEnvironment = TestEnvironment.loadEnvironmentForDirectory(directory, false);
    }

    public KeYTestGenTest(String directory,
                          boolean loadSubDirectories,
                          String... files) throws KeYInterfaceException, IOException {

        testEnvironment = TestEnvironment.loadEnvironmentForDirectory(directory, false, files);
    }

    public KeYTestGenTest() {
        testEnvironment = null;
    }

    protected IExecutionNode getFirstSymbolicNodeForStatement(String method,
                                                              String statement) throws ProofInputException {

        IExecutionStart symbolicTree = getSymbolicTreeForMethod(method);
        Assert.assertTrue(symbolicTree != null);

        List<IExecutionNode> symbolicNodes = getSymbolicExecutionNode(symbolicTree, statement);
        Assert.assertTrue(symbolicNodes != null);
        Assert.assertFalse(symbolicNodes.isEmpty());

        // Get the first node corresponding to the statement
        IExecutionNode targetNode = symbolicNodes.get(0);

        return targetNode;
    }

    protected List<IExecutionNode> getSymbolicNodesForStatement(String method,
                                                                String statement) throws ProofInputException {

        IExecutionStart symbolicTree = getSymbolicTreeForMethod(method);
        Assert.assertTrue(symbolicTree != null);

        List<IExecutionNode> symbolicNodes = getSymbolicExecutionNode(symbolicTree, statement);
        Assert.assertTrue(symbolicNodes != null);
        Assert.assertFalse(symbolicNodes.isEmpty());

        return symbolicNodes;
    }

    protected IExecutionStart getSymbolicTreeForMethod(String identifier) {
        IExecutionStart tree = testEnvironment.getSymbolicTreeForNode(identifier);
        Assert.assertNotNull("Could not find tree for method: " + identifier, tree);
        return tree;
    }

    protected static class SMTSettings implements de.uka.ilkd.key.smt.SMTSettings {

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

            return PathConfig.getKeyConfigDir() + File.separator + "smt_formula";
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

    protected IExecutionMethodCall getMethodCallNode(final IExecutionStart root) {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            if (next instanceof IExecutionMethodCall) {
                return (IExecutionMethodCall) next;
            }
        }
        return null;
    }

    protected void printBranchNodes(final IExecutionStart root) throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            if (next instanceof IExecutionBranchStatement) {
                System.out.println(((IExecutionBranchStatement) next).getActivePositionInfo());
                System.out.println(((IExecutionBranchStatement) next).getActiveStatement());
                printSingleNode(next);
            }
        }
    }

    protected void printExecutionReturnStatementNodes(final IExecutionStart root) throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            if (next instanceof ExecutionMethodReturn) {
                printSingleNode(next);
            }
        }
    }

    protected void printExecutionStatementNodes(final IExecutionStart root) throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            if (next instanceof IExecutionStatement) {
                printSingleNode(next);
            }
        }
    }

    protected void printExecutionStateNodes(final IExecutionStart root) throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(root);

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

    protected void printJavaInfo(final IExecutionStart root) {

        final JavaInfo info = root.getMediator().getJavaInfo();

        for (final KeYJavaType type : info.getAllKeYJavaTypes()) {
            System.out.println(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS);

        }
    }

    protected void printNamespaceProgramVariables(final SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment) {

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

    protected void printNamespaceVariables(final SymbolicExecutionEnvironment<CustomConsoleUserInterface> environment) {

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

    protected void printSingleNode(final IExecutionNode node) throws ProofInputException {

        System.out
              .println("\nNode " + node.getName() + "\nType: " + node.getClass() + "\nPath condition " + node.getPathCondition() + "\nHuman readable: " + node
                      .getFormatedPathCondition()
                      .replaceAll("\n|\t", "") + "\nAddress: " + node.hashCode());

        System.out.println("Children:");
        for (final IExecutionNode child : node.getChildren()) {
            System.out.println("\t" + child.getName());
            System.out.println("\t" + child.getClass());
            System.out.println("\t" + child.getFormatedPathCondition());
        }
    }

    protected void printSymbolicExecutionTree(final IExecutionStart root) throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            printSingleNode(next);
        }
    }

    protected void printSymbolicExecutionTreePathConditions(final IExecutionStart root) throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(root);

        while (iterator.hasNext()) {

            final IExecutionNode next = iterator.next();

            if (next instanceof IExecutionStateNode<?>) {

                final IExecutionStateNode<?> stateNode = (IExecutionStateNode<?>) next;
                System.out
                      .println("Node " + stateNode.getName() + "\nPath condition " + stateNode.getPathCondition() + "\nHuman readable: " + stateNode
                              .getFormatedPathCondition()
                              .replaceAll("\n|\t", "") + "\n");
            }
        }
    }

    protected void printTermAST(final Term term) {

        System.out.println("\nTerm: " + term + "\nhas runtime class: " + term.getClass() + "\nand sort: " + term.sort()
                                                                                                                .declarationString() + "\n\twith runtime type: " + term
                .sort()
                .getClass() + "\nand op: " + term.op() + "\n\twith runtime type: " + term.op()
                                                                                         .getClass() + "\n" + "Number of subs: " + term
                .arity() + "\n");

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
     * @param rootNode  starting node for the symbolic execution tree
     * @param statement the statement to search for
     * @return
     * @throws ProofInputException
     */
    protected ArrayList<IExecutionNode> getSymbolicExecutionNode(final IExecutionStart rootNode,
                                                                 final String statement) throws ProofInputException {

        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(rootNode);

        final ArrayList<IExecutionNode> nodes = new ArrayList<IExecutionNode>();

        while (iterator.hasNext()) {
            final IExecutionNode next = iterator.next();
            if (next.getName().trim().equalsIgnoreCase(statement + ";")) {
                nodes.add(next);
            }
        }

        for (IExecutionNode node : nodes) {
            Assert.assertNotNull(node);
        }

        return nodes;
    }
}