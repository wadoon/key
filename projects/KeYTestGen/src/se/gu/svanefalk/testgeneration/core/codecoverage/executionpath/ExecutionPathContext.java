package se.gu.svanefalk.testgeneration.core.codecoverage.executionpath;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

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

    private static class ExecutionContextBuilder {

        private static boolean isBranchCondition(final IExecutionNode node) {

            return node instanceof IExecutionBranchCondition;
        }

        /**
         * Stack to hold partially constructed PathBranchNode ->
         * PathBranchCondition mappings, also divided at branching points in the
         * code.
         */
        final Stack<Map<SourceElement, List<IExecutionBranchCondition>>> branchedPathConditionMappings = new Stack<Map<SourceElement, List<IExecutionBranchCondition>>>();

        Stack<ExecutionBranch> branchesForSubtree = new Stack<ExecutionBranch>();

        List<ExecutionBranch> executionBranches = new LinkedList<>();
        /**
         * The ExecutionPath currently being constructed
         */
        ExecutionPath executionPath = new ExecutionPath();
        /**
         * The generated execution paths.
         */
        final List<ExecutionPath> executionPaths = new LinkedList<ExecutionPath>();
        /**
         * Data structures for constructing the ExecutionBranches, together with
         * associated metadata.
         */
        Map<ExecutionBranch, List<ExecutionPath>> executionPathsForBranch = new HashMap<>();

        /**
         * The last seen PathBranchNode
         */
        Stack<SourceElement> lastSeenPathBranchNode = new Stack<SourceElement>();

        SourceElement lastVisitedSourceElement = null;

        /**
         * Used in order to store the path nodes of the execution path currently
         * being constructed.
         */
        Set<SourceElement> nodesVisitedByCurrentPath = new HashSet<SourceElement>();

        /**
         * Stack to hold partial execution paths, i.e. a list of program nodes
         * leading up to a branching statement in the code (as these may be part
         * of several different execution paths depending on the outcome of the
         * branching statement in question).
         */
        final Stack<Set<SourceElement>> partialExecutionPaths = new Stack<Set<SourceElement>>();

        /**
         * For a given path, this map stores a mapping between a PathBranchNode
         * and a set of PathBranchCondition instances which are being taken from
         * the PathBranchNode by this particular path.
         */
        Map<SourceElement, List<IExecutionBranchCondition>> pathConditionMappings = new HashMap<SourceElement, List<IExecutionBranchCondition>>();

        /**
         * Flag indicating if we are currently returning from walking a subtree
         * of a branching node.
         */
        boolean returningFromBranch = false;

        /**
         * Mapping between SourceElements and their corresponding symbolic
         * nodes.
         */
        final Map<SourceElement, List<IExecutionNode>> symbolicNodesForSourceElements = new HashMap<SourceElement, List<IExecutionNode>>();

        /**
         * Set of the SourceElements which have already been seen.
         */
        final Set<SourceElement> visitedNodes = new HashSet<SourceElement>();

        /**
         * Constructs a new {@link ExecutionPathContext} instance for a symbolic
         * execution tree.
         * 
         * @param root
         *            root node of the symbolic execution tree
         * @return the execution context
         */
        public ExecutionPathContext build(final IExecutionStartNode root) {

            // FIXME: This method is an absolute terror.

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
                if (isExecutionPathNode(node)) {

                    /*
                     * If we are returning from a branch, continue building from
                     * the list of nodes visited by the execution path which
                     * branched here.
                     */
                    if (returningFromBranch) {
                        nodesVisitedByCurrentPath = partialExecutionPaths.pop();
                        pathConditionMappings = branchedPathConditionMappings.pop();
                        executionPath = new ExecutionPath();

                        /*
                         * Pop, from the stack of seen ExecutionBranch
                         * instances, all the ones below the parent of this
                         * node.
                         */
                        final SourceElement parent = findParentExecutionBranch(node);
                        while (!branchesForSubtree.isEmpty()) {
                            final ExecutionBranch branch = branchesForSubtree.peek();
                            if (branch.getSecond() != parent) {
                                branchesForSubtree.pop();
                            } else {
                                break;
                            }
                        }

                        /*
                         * Set the last visited node to be the last visited
                         * branch node
                         */
                        lastVisitedSourceElement = lastSeenPathBranchNode.peek();

                        returningFromBranch = false;
                    }

                    /*
                     * Process a node which corresponds to a program statement
                     */
                    if (isProgramStatementNode(node)) {

                        /*
                         * Check if we have already visited this node. If not,
                         * add it to the set of visited nodes.
                         */
                        final SourceElement currentElement = getActiveStatement(node);
                        currentElement.getStartPosition();
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
                         * Add the concrete node to the list of nodes covered by
                         * the current execution path.
                         */
                        nodesVisitedByCurrentPath.add(currentElement);

                        /*
                         * Construct the ExecutionBranch for this node, by
                         * associating it with the last node visited before it
                         * (i.e. the last element is the element which the
                         * branch leads FROM, the current element will be the
                         * element it leads TO).
                         * 
                         * Further, associate this branch with the current
                         * execution path, showing that this path covers this
                         * branch.
                         */
                        if (lastVisitedSourceElement != null) {

                            final ExecutionBranch executionBranch = new ExecutionBranch(
                                    lastVisitedSourceElement, currentElement);

                            executionBranches.add(executionBranch);

                            /*
                             * Add the current branch to the stack of branches
                             * for this subtree.
                             */
                            branchesForSubtree.push(executionBranch);
                        }

                        /*
                         * Set the current node as the last visited node.
                         */
                        lastVisitedSourceElement = currentElement;

                        /*
                         * If this node is an execution branch node, we will
                         * node to store it so that we can later return to it.
                         * We push it once upon the stack for each child of the
                         * branching node, since we will have to return to it
                         * that many times.
                         */
                        if (isExecutionBranchNode(node)
                                || isBranchingNode(node)) {
                            for (int i = 0; i < node.getChildren().length; i++) {
                                lastSeenPathBranchNode.push(currentElement);
                            }
                        }
                    }

                    /*
                     * If the node is a branching statement, store the current
                     * list of visited path nodes so that we can later retrieve
                     * them to construct execution paths for other branches of
                     * this node.
                     */
                    if (isBranchingNode(node)) {

                        for (int i = 0; i < (node.getChildren().length - 1); i++) {
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
                     * If the current node is a branch node condition, then we
                     * will need to associate it with this particular execution
                     * path. We do so by binding it to the LAST branch node
                     * which has been visited by this execution path.
                     */
                    if (ExecutionContextBuilder.isBranchCondition(node)) {
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
                     * If this is a terminating node, construct and store the
                     * final execution path and continue walking the tree.
                     */
                    if (isTerminatingNode(node)) {
                        executionPath.setCoveredNodes(nodesVisitedByCurrentPath);
                        executionPath.setBranchConditionMappings(pathConditionMappings);
                        executionPath.setTerminatingNode(node);
                        executionPaths.add(executionPath);

                        /*
                         * Retroactively associate this path with each branch
                         * visited so far on this subtree.
                         */
                        for (final ExecutionBranch executionBranch : branchesForSubtree) {
                            List<ExecutionPath> pathsForBranch = executionPathsForBranch.get(executionBranch);
                            if (pathsForBranch == null) {
                                pathsForBranch = new LinkedList<>();
                                executionPathsForBranch.put(executionBranch,
                                        pathsForBranch);
                            }
                            pathsForBranch.add(executionPath);
                        }

                        returningFromBranch = true;
                    }
                }
            }

            return new ExecutionPathContext(executionPaths,
                    executionPathsForBranch, visitedNodes, executionBranches);
        }

        private SourceElement findParentExecutionBranch(IExecutionNode node) {

            while (true) {
                if (node.getParent() instanceof AbstractExecutionStateNode) {
                    return ((AbstractExecutionStateNode) node.getParent()).getActiveStatement();
                } else {
                    node = node.getParent();
                }
            }
        }

        private SourceElement getActiveStatement(final IExecutionNode node) {
            final AbstractExecutionStateNode abstractExecutionStateNode = (AbstractExecutionStateNode) node;
            return abstractExecutionStateNode.getActiveStatement();
        }

        /**
         * 
         * @param node
         *            the node
         * @return true if the node has more than one child, false otherwise
         */
        private boolean isBranchingNode(final IExecutionNode node) {

            return node.getChildren().length > 1;
        }

        private boolean isExecutionBranchNode(final IExecutionNode node) {
            return node instanceof IExecutionBranchNode;
        }

        private boolean isExecutionPathNode(final IExecutionNode node) {

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
        private boolean isProgramStatementNode(final IExecutionNode node) {
            return node instanceof AbstractExecutionStateNode;
        }

        private boolean isTerminatingNode(final IExecutionNode node) {

            return node instanceof IExecutionTermination;
        }
    }

    public static ExecutionPathContext constructExecutionContext(
            final IExecutionStartNode root) {
        return new ExecutionContextBuilder().build(root);
    }

    private final List<ExecutionBranch> executionBranches;

    /**
     * The {@link ExecutionPathContext} instances which are part of this
     * context.
     */
    private final List<ExecutionPath> executionPaths;

    private final Map<ExecutionBranch, List<ExecutionPath>> executionPathsForBranch;

    private final Set<SourceElement> visitedProgramNodes;

    public ExecutionPathContext(
            final List<ExecutionPath> executionPaths,
            final Map<ExecutionBranch, List<ExecutionPath>> executionPathsForBranch,
            final Set<SourceElement> visitedProgramNodes,
            final List<ExecutionBranch> executionBranches) {
        super();
        this.executionPaths = executionPaths;
        this.executionPathsForBranch = executionPathsForBranch;
        this.visitedProgramNodes = visitedProgramNodes;
        this.executionBranches = executionBranches;
    }

    /**
     * @return the executionBranches
     */
    public List<ExecutionBranch> getExecutionBranches() {
        return executionBranches;
    }

    /**
     * @return the executionPaths
     */
    public List<ExecutionPath> getExecutionPaths() {
        return executionPaths;
    }

    public List<ExecutionPath> getExecutionPathsForBranch(
            final ExecutionBranch branch) {
        return executionPathsForBranch.get(branch);
    }

    /**
     * @return the visitedProgramNodes
     */
    public Set<SourceElement> getVisitedProgramNodes() {
        return visitedProgramNodes;
    }
}