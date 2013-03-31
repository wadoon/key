package se.gu.svanefalk.testgeneration.core.codecoverage.executionpath;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
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
     * The {@link ExecutionPathContext} instances which are part of this
     * context.
     */
    private final List<ExecutionPath> executionPaths;

    private final Map<ExecutionBranch, List<ExecutionPath>> executionPathsForBranch;

    private final Set<SourceElement> visitedProgramNodes;

    private final List<ExecutionBranch> executionBranches;

    public ExecutionPathContext(List<ExecutionPath> executionPaths,
            Map<ExecutionBranch, List<ExecutionPath>> executionPathsForBranch,
            Set<SourceElement> visitedProgramNodes,
            List<ExecutionBranch> executionBranches) {
        super();
        this.executionPaths = executionPaths;
        this.executionPathsForBranch = executionPathsForBranch;
        this.visitedProgramNodes = visitedProgramNodes;
        this.executionBranches = executionBranches;
    }

    /**
     * Constructs a new {@link ExecutionPathContext} instance for a symbolic
     * execution tree.
     * 
     * @param root
     *            root node of the symbolic execution tree
     * @return the execution context
     */
    public static ExecutionPathContext constructExecutionContext(
            final IExecutionStartNode root) {

        // FIXME: This method is an absolute terror.

        /*
         * The ExecutionPath currently being constructed
         */
        ExecutionPath executionPath = new ExecutionPath();

        /*
         * Flag indicating if we are currently returning from walking a subtree
         * of a branching node.
         */
        boolean returningFromBranch = false;

        /*
         * Set of the SourceElements which have already been seen.
         */
        final Set<SourceElement> visitedNodes = new HashSet<SourceElement>();

        /*
         * Data structures for constructing the ExecutionBranches, together with
         * associated metadata.
         */
        Map<ExecutionBranch, List<ExecutionPath>> executionPathsForBranch = new HashMap<>();
        List<ExecutionBranch> executionBranches = new LinkedList<>();
        Stack<SourceElement> lastVisitedSourceElement = new Stack<>();

        /*
         * Used in order to store the path nodes of the execution path currently
         * being constructed.
         */
        Set<SourceElement> nodesVisitedByCurrentPath = new HashSet<SourceElement>();

        /*
         * Mapping between SourceElements and their corresponding symbolic
         * nodes.
         */
        final Map<SourceElement, List<IExecutionNode>> symbolicNodesForSourceElements = new HashMap<SourceElement, List<IExecutionNode>>();

        /*
         * Stack to hold partial execution paths, i.e. a list of program nodes
         * leading up to a branching statement in the code (as these may be part
         * of several different execution paths depending on the outcome of the
         * branching statement in question).
         */
        final Stack<Set<SourceElement>> partialExecutionPaths = new Stack<Set<SourceElement>>();

        /*
         * For a given path, this map stores a mapping between a PathBranchNode
         * and a set of PathBranchCondition instances which are being taken from
         * the PathBranchNode by this particular path.
         */
        Map<SourceElement, List<IExecutionBranchCondition>> pathConditionMappings = new HashMap<SourceElement, List<IExecutionBranchCondition>>();

        /*
         * Stack to hold partially constructed PathBranchNode ->
         * PathBranchCondition mappings, also divided at branching points in the
         * code.
         */
        final Stack<Map<SourceElement, List<IExecutionBranchCondition>>> branchedPathConditionMappings = new Stack<Map<SourceElement, List<IExecutionBranchCondition>>>();

        /*
         * The generated execution paths.
         */
        final List<ExecutionPath> executionPaths = new LinkedList<ExecutionPath>();

        /*
         * The last seen PathBranchNode
         */
        Stack<SourceElement> lastSeenPathBranchNode = new Stack<SourceElement>();

        /*
         * Iterator for walking the symbolic execution tree.
         */
        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(
                root);

        /*
         * Iteratively construct the execution paths.
         */
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
                    nodesVisitedByCurrentPath = partialExecutionPaths.pop();
                    pathConditionMappings = branchedPathConditionMappings.pop();
                    lastSeenPathBranchNode.pop();
                    executionPath = new ExecutionPath();
                    returningFromBranch = false;
                }

                /*
                 * Process a node which corresponds to a program statement
                 */
                if (ExecutionPathContext.isProgramStatementNode(node)) {

                    /*
                     * Check if we have already visited this node. If not, add
                     * it to the set of visited nodes.
                     */
                    final SourceElement currentElement = getActiveStatement(node);
                    if (!visitedNodes.contains(currentElement)) {
                        visitedNodes.add(currentElement);
                    }

                    /*
                     * Associate the current symbolic node with the current
                     * program element.
                     */
                    List<IExecutionNode> symbolicNodes = symbolicNodesForSourceElements.get(currentElement);
                    if (symbolicNodes == null) {
                        symbolicNodes = new LinkedList<IExecutionNode>();
                        symbolicNodesForSourceElements.put(currentElement,
                                symbolicNodes);
                    }
                    symbolicNodes.add(node);

                    /*
                     * Add the concrete node to the list of nodes covered by the
                     * current execution path.
                     */
                    nodesVisitedByCurrentPath.add(currentElement);

                    /*
                     * Construct the ExecutionBranch for this node, by
                     * associating it with the last node visited before it.
                     * Further, associate this branch with the current execution
                     * path, showing that this path covers this branch.
                     */
                    if (!lastVisitedSourceElement.isEmpty()) {
                        SourceElement lastElement = lastVisitedSourceElement.pop();

                        ExecutionBranch executionBranch = new ExecutionBranch(
                                lastElement, currentElement);

                        List<ExecutionPath> pathsForBranch = executionPathsForBranch.get(executionBranch);
                        if (pathsForBranch == null) {
                            pathsForBranch = new LinkedList<>();
                            executionPathsForBranch.put(executionBranch,
                                    pathsForBranch);
                        }
                        pathsForBranch.add(executionPath);
                        executionBranches.add(executionBranch);
                    }

                    /*
                     * Set the current node as the last visited node.
                     */
                    for (int i = 0; i < node.getChildren().length; i++) {
                        lastVisitedSourceElement.push(currentElement);
                    }

                    /*
                     * If this node is an execution branch node, we will node to
                     * store it so that we can later return to it. We push it
                     * once upon the stack for each child of the branching node,
                     * since we will have to return to it that many times.
                     */
                    if (isExecutionBranchNode(node)) {
                        for (int i = 0; i < node.getChildren().length; i++) {
                            lastSeenPathBranchNode.push(currentElement);
                        }
                    }
                }

                /*
                 * If the node is a branching statement, store the current list
                 * of visited path nodes so that we can later retrieve them to
                 * construct execution paths for other branches of this node.
                 */
                if (ExecutionPathContext.isBranchingNode(node)) {

                    for (int i = 0; i < node.getChildren().length - 1; i++) {
                        final Set<SourceElement> oldExecutionPath = new HashSet<SourceElement>();
                        oldExecutionPath.addAll(nodesVisitedByCurrentPath);
                        partialExecutionPaths.push(oldExecutionPath);

                        /*
                         * Do the same for the pathcondition mappings.
                         */
                        final Map<SourceElement, List<IExecutionBranchCondition>> oldPathConditionMappings = new HashMap<SourceElement, List<IExecutionBranchCondition>>();
                        oldPathConditionMappings.putAll(pathConditionMappings);
                        branchedPathConditionMappings.push(oldPathConditionMappings);
                    }
                }

                /*
                 * If the current node is a branch node condition, then we will
                 * need to associate it with this particular execution path. We
                 * do so by binding it to the LAST branch node which has been
                 * visited by this execution path.
                 */
                if (isBranchCondition(node)) {
                    List<IExecutionBranchCondition> pathBranchConditions = pathConditionMappings.get(lastSeenPathBranchNode);
                    if (pathBranchConditions == null) {
                        pathBranchConditions = new LinkedList<IExecutionBranchCondition>();
                        pathConditionMappings.put(
                                lastSeenPathBranchNode.peek(),
                                pathBranchConditions);
                    }
                    pathBranchConditions.add((IExecutionBranchCondition) node);
                }

                /*
                 * If this is a terminating node, construct and store the final
                 * execution path and continue walking the tree.
                 */
                if (ExecutionPathContext.isTerminatingNode(node)) {
                    executionPath.setCoveredNodes(nodesVisitedByCurrentPath);
                    executionPath.setBranchConditionMappings(pathConditionMappings);
                    executionPath.setTerminatingNode(node);
                    executionPaths.add(executionPath);

                    lastVisitedSourceElement.pop();

                    returningFromBranch = true;
                }
            }
        }

        return new ExecutionPathContext(executionPaths,
                executionPathsForBranch, visitedNodes, executionBranches);
    }

    /**
     * @return the visitedProgramNodes
     */
    public Set<SourceElement> getVisitedProgramNodes() {
        return visitedProgramNodes;
    }

    public List<ExecutionPath> getExecutionPathsForBranch(ExecutionBranch branch) {
        return executionPathsForBranch.get(branch);
    }

    /**
     * @return the executionPaths
     */
    public List<ExecutionPath> getExecutionPaths() {
        return executionPaths;
    }

    /**
     * @return the executionBranches
     */
    public List<ExecutionBranch> getExecutionBranches() {
        return executionBranches;
    }

    private static SourceElement getActiveStatement(IExecutionNode node) {
        AbstractExecutionStateNode abstractExecutionStateNode = (AbstractExecutionStateNode) node;
        return abstractExecutionStateNode.getActiveStatement();
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

    private static boolean isExecutionBranchNode(IExecutionNode node) {
        return node instanceof IExecutionBranchNode;
    }

    private static boolean isExecutionPathNode(final IExecutionNode node) {

        return (node instanceof IExecutionStatement)
                || (node instanceof IExecutionBranchNode)
                || (node instanceof IExecutionBranchCondition)
                || (node instanceof IExecutionTermination);
    }

    private static boolean isBranchCondition(final IExecutionNode node) {

        return node instanceof IExecutionBranchCondition;
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