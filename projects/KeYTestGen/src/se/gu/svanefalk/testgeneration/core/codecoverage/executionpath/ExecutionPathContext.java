package se.gu.svanefalk.testgeneration.core.codecoverage.executionpath;

import java.util.Calendar;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.impl.AbstractExecutionStateNode;

public class ExecutionPathContext {

    /**
     * Used for constructing {@link PathNode} instances.
     */
    private final static PathNodeFactory nodeFactory = PathNodeFactory.INSTANCE;

    /**
     * An index over which {@link PathNode} instances in this context are
     * covered by which {@link ExecutionPath} instance or instances.
     */
    private final Map<PathNode, List<ExecutionPath>> executionPathsForNode;

    /**
     * The {@link ExecutionPath} instances which are part of this context.
     */
    private final List<ExecutionPath> executionPaths;

    private ExecutionPathContext(
            Map<PathNode, List<ExecutionPath>> executionPathsForNode,
            List<ExecutionPath> executionPaths) {
        super();
        this.executionPathsForNode = executionPathsForNode;
        this.executionPaths = executionPaths;
    }

    /**
     * Constructs a new {@link ExecutionContext} instance for a symbolic
     * execution tree.
     * 
     * @param root
     *            root node of the symbolic execution tree
     * @return the execution context
     */
    public static ExecutionPathContext constructExecutionContext(
            final IExecutionStartNode root) {

        boolean returningFromBranch = false;

        /*
         * Maps each {@link PathNode} instance in this context to the set of
         * {@link ExecutionPath} instances which cover it.
         */
        final Map<PathNode, List<ExecutionPath>> executionPathsForNode = new HashMap<PathNode, List<ExecutionPath>>();

        /*
         * The ExecutionPath currently being constructed
         */
        final ExecutionPath executionPath = new ExecutionPath();

        /*
         * Map over which program statements have already been seen.
         */
        final Map<String, PathNode> seenPathNodes = new HashMap<String, PathNode>();

        /*
         * Stack to hold partial execution paths, i.e. a list of program nodes
         * leading up to a branching statement in the code (as these may be part
         * of several different execution paths depending on the outcome of the
         * branching statement in question).
         */
        final Stack<List<PathNode>> branchedExecutionPaths = new Stack<List<PathNode>>();

        /*
         * The generated execution paths.
         */
        final List<ExecutionPath> executionPaths = new LinkedList<ExecutionPath>();

        /*
         * Used in order to store the path nodes of the execution path currently
         * being constructed.
         */
        List<PathNode> visitedNodesBuffer = new LinkedList<PathNode>();

        /*
         * Iterator for walking the symbolic execution tree.
         */
        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(
                root);

        /*
         * Iteratively construct the execution paths.
         */
        long millis = Calendar.getInstance().getTimeInMillis();
        while (iterator.hasNext()) {

            final IExecutionNode node = iterator.next();

            /*
             * Work only with the symbolic execution nodes corresponding to
             * actual program statements.
             */
            if (ExecutionPathContext.isExecutionPathNode(node)) {

                /*
                 * If we are returning from a branch, continue building from the
                 * list of nodes visited by the execution path which branched
                 * here.
                 */
                if (returningFromBranch) {
                    millis = Calendar.getInstance().getTimeInMillis();
                    visitedNodesBuffer = branchedExecutionPaths.pop();
                    returningFromBranch = false;
                }

                /*
                 * Check if the current symbolic node corresponds to a real
                 * program node which we have already seen. Create a
                 * corresponding node for it if so is not the case. Connect the
                 * concrete node with the symbolic node.
                 */
                if (ExecutionPathContext.isProgramStatementNode(node)) {

                    final String pathNodeIdentifier = ExecutionPathContext.getUniqueIdentifier((AbstractExecutionStateNode) node);

                    PathNode pathNode = seenPathNodes.get(pathNodeIdentifier);

                    if (pathNode == null) {
                        pathNode = ExecutionPathContext.nodeFactory.constructExecutionNode(node);
                        seenPathNodes.put(pathNodeIdentifier, pathNode);
                    }
                    pathNode.addCorrespondingSymbolicNode(node);

                    /*
                     * Add the concrete node to the list of nodes covered by the
                     * current execution path.
                     */
                    visitedNodesBuffer.add(pathNode);

                    /*
                     * Register that the given node is now covered by this
                     * execution path.
                     */
                    List<ExecutionPath> pathsForNode = executionPathsForNode.get(pathNode);
                    if (pathsForNode == null) {
                        pathsForNode = new LinkedList<ExecutionPath>();
                        executionPathsForNode.put(pathNode, pathsForNode);
                    }
                    pathsForNode.add(executionPath);
                }

                /*
                 * If the node is a branching statement, store the current list
                 * of visited path nodes so that we can later retrieve them to
                 * construct execution paths for other branches of this node.
                 */
                if (ExecutionPathContext.isBranchingNode(node)) {
                    final List<PathNode> oldExecutionPath = new LinkedList<PathNode>();
                    oldExecutionPath.addAll(visitedNodesBuffer);
                    branchedExecutionPaths.push(oldExecutionPath);
                }

                /*
                 * If this is a terminating node, construct and store the final
                 * execution path and continue walking the tree.
                 */
                if (ExecutionPathContext.isTerminatingNode(node)) {
                    executionPath.setCoveredNodes(visitedNodesBuffer);
                    executionPath.setTerminatingNode(node);
                    executionPaths.add(executionPath);
                    returningFromBranch = true;

                    System.out.println("Constructing path: "
                            + (Calendar.getInstance().getTimeInMillis() - millis));
                    millis = Calendar.getInstance().getTimeInMillis();
                }
            }
        }

        return new ExecutionPathContext(executionPathsForNode, executionPaths);
    }

    /**
     * Computes a unique identifier for an instance of
     * {@link AbstractExecutionStateNode}.
     * 
     * @param node
     *            the node
     * @return the identifier
     */
    private static String getUniqueIdentifier(
            final AbstractExecutionStateNode node) {

        final StringBuilder toReturn = new StringBuilder();
        final PositionInfo positionInfo = node.getActivePositionInfo();
        final SourceElement elem = node.getActiveStatement();

        String stuff = "" + positionInfo.getStartPosition() + positionInfo.getEndPosition() + positionInfo.getRelativePosition();

        toReturn.append(elem.toString());
        toReturn.append(positionInfo.getStartPosition().toString());
        toReturn.append(positionInfo.getEndPosition().toString());
        toReturn.append(positionInfo.getRelativePosition().toString());
        return toReturn.toString();
    }

    /**
     * 
     * @param node
     *            the node
     * @return true if the node has more than one child, false otherwise
     */
    private static boolean isBranchingNode(final IExecutionNode node) {

        return node.getChildren().length > 1;
    }

    private static boolean isExecutionPathNode(final IExecutionNode node) {

        return (node instanceof IExecutionStatement)
                || (node instanceof IExecutionBranchNode)
                || (node instanceof IExecutionBranchCondition)
                || (node instanceof IExecutionTermination);
    }

    /**
     * @param node
     *            the node
     * @return true if the node corresponds to a program statement, false
     *         otherwise
     */
    private static boolean isProgramStatementNode(final IExecutionNode node) {
        return node instanceof AbstractExecutionStateNode;
    }

    private static boolean isTerminatingNode(final IExecutionNode node) {

        return node instanceof IExecutionTermination;
    }
}