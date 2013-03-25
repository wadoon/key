package se.gu.svanefalk.testgeneration.core.codecoverage.pathcontext;

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

    private final static PathNodeFactory nodeFactory = PathNodeFactory.INSTANCE;

    public static ExecutionPathContext constructExecutionContext(
            final IExecutionStartNode root) {

        boolean returningFromBranch = false;

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
         * Iteratively construct the execution path models.
         */
        while (iterator.hasNext()) {

            final IExecutionNode node = iterator.next();
            long millis = Calendar.getInstance().getTimeInMillis();
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

                    millis = Calendar.getInstance().getTimeInMillis();
                    final String pathNodeIdentifier = ExecutionPathContext
                            .getUniqueIdentifier((AbstractExecutionStateNode) node);
                    System.out
                            .println("Getting identifier: "
                                    + (Calendar.getInstance().getTimeInMillis() - millis));

                    PathNode pathNode = seenPathNodes.get(pathNodeIdentifier);

                    if (pathNode == null) {
                        pathNode = ExecutionPathContext.nodeFactory
                                .constructExecutionNode(node);
                        seenPathNodes.put(pathNodeIdentifier, pathNode);
                    }
                    pathNode.addCorrespondingSymbolicNode(node);

                    /*
                     * Add the concrete node to the list of nodes covered by the
                     * current execution path.
                     */
                    visitedNodesBuffer.add(pathNode);
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

                    final ExecutionPath executionPath = new ExecutionPath(
                            visitedNodesBuffer, node);
                    executionPaths.add(executionPath);
                    returningFromBranch = true;

                }
            }
        }

        return null;
    }

    private static String getUniqueIdentifier(
            final AbstractExecutionStateNode node) {

        final StringBuilder toReturn = new StringBuilder();
        final PositionInfo positionInfo = node.getActivePositionInfo();
        final SourceElement elem = node.getActiveStatement();

        toReturn.append(elem.toString());
        toReturn.append(positionInfo.getStartPosition().toString());
        toReturn.append(positionInfo.getEndPosition().toString());
        toReturn.append(positionInfo.getRelativePosition().toString());
        return toReturn.toString();
    }

    private static boolean isBranchingNode(final IExecutionNode node) {

        return node.getChildren().length > 1;
    }

    private static boolean isExecutionPathNode(final IExecutionNode node) {

        return (node instanceof IExecutionStatement)
                || (node instanceof IExecutionBranchNode)
                || (node instanceof IExecutionBranchCondition)
                || (node instanceof IExecutionTermination);
    }

    private static boolean isProgramStatementNode(final IExecutionNode node) {
        return node instanceof AbstractExecutionStateNode;
    }

    private static boolean isTerminatingNode(final IExecutionNode node) {

        return node instanceof IExecutionTermination;
    }

    private ExecutionPathContext(final ExecutionPath[] executionPaths) {
        super();
    }
}