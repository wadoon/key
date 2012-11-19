package de.uka.ilkd.key.testgeneration.codecoverage;

import java.io.PrintWriter;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

/**
 * Encapsultates logic needed to achieve code coverage for a given symbolic execution tree.
 * 
 * @author christopher
 */
public class PathAnalyzer {

    public enum COVERAGE_CRITERIA {

    }

    /**
     * <p>
     * Returns a set of {@link IExecutionNode} instances, s.t. generating a test case covering each
     * of these nodes will satisfy Statement Coverage for this symbolic execution tree.
     * </p>
     * <p>
     * Statement Coverage is satisfied iff. a set of test cases is provided, s.t. the execution of
     * these test cases will lead to each statement in the IUT being executed at least once.
     * </p>
     * 
     * @param root
     *            the root of the symbolic execution tree
     * @return
     */
    public List<IExecutionNode> getStatementCoveringNodes(IExecutionStartNode root) {

        /*
         * Due to the way symbolic execution trees are implemented (do not confuse them with
         * standard execution trees), simply gathering all return statements should guarantee full
         * statement coverage. See separate proof.
         */
        ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(root);
        List<IExecutionNode> nodes = new LinkedList<IExecutionNode>();

        while (iterator.hasNext()) {
            IExecutionNode next = iterator.next();
            if (next instanceof IExecutionMethodReturn) {
                nodes.add(next);
            }
        }
        return nodes;
    }

    /**
     * <p>
     * Returns a set of {@link IExecutionNode} instances, s.t. generating a test case covering each
     * of these nodes will satisfy Branch Coverage for this symbolic execution tree.
     * </p>
     * <p>
     * Branch Coverage for a test suite T over a program P is satisfied iff. the execution of each
     * test case t in T will cause each possible path between two statement in P to be taken at
     * least once.
     * </p>
     * 
     * @param root
     *            the root of the symbolic execution tree
     * @return
     */
    public List<IExecutionNode> getBranchCoveringNodes(IExecutionStartNode root) {

        throw new UnsupportedOperationException("Not implemented yet");
    }

    /**
     * <p>
     * Returns a set of {@link IExecutionNode} instances, s.t. generating a test case covering each
     * of these nodes will satisfy Path Coverage for this symbolic execution tree.
     * </p>
     * <p>
     * Path Coverage for a test suite T over a program P is satisfied iff. the execution of each
     * test case t in T will cause each feasible execution path throughout the tree to be taken at
     * least once.
     * </p>
     * <p>
     * NOTE: Path coverage is not feasible to obtain for many programs. Furthermore, for programs
     * involving loops, full path coverage is usually impossible to achieve, since the symbolic
     * representation of a loop sequence results in an infinite number of possible execution paths.
     * In that event, this method returns <code>null</code>.
     * </p>
     * 
     * @param root
     *            the root of the symbolic execution tree
     * @return
     */
    public List<IExecutionNode> getPathCoveringNodes(IExecutionStartNode root) {

        throw new UnsupportedOperationException("Not implemented yet");
    }

    /**
     * <p>
     * Returns a set of {@link IExecutionNode} instances, s.t. generating a test case covering each
     * of these nodes will satisfy Decision Coverage for this symbolic execution tree.
     * </p>
     * <p>
     * Decision Coverage for a test suite T over a program P is satisfied iff. the execution of each
     * test case t in T will cause each branching statement in the code (such as if...else
     * statements and the like) to evaluate at least once to true, and at least once to false.
     * <p>
     * To illustrate this, consider the following:
     * <p>
     * <code>
     * public int max(int a, int b) {
     * <br>if(a >= b) 
     * <br><return a; 
     * <br>else 
     * <br>return b;
     * <br>}
     * </code>
     * <p>
     * In the above, our only branching condition is the condition in the if-statement,
     * <code>a >= b</code>. Accordingly, we need to provide testcases s.t. this will once evaluate
     * to true (i.e. a >= b) and at least once to false (i.e. a < b).
     * 
     * @param root
     *            the root of the symbolic execution tree
     * @return
     */
    public List<IExecutionNode> getDecisionCoveringNodes(IExecutionStartNode root) {

        throw new UnsupportedOperationException("Not implemented yet");
    }

    /**
     * <p>
     * Returns a set of {@link IExecutionNode} instances, s.t. generating a test case covering each
     * of these nodes will satisfy Condition Coverage for this symbolic execution tree.
     * <p>
     * Condition Coverage for a test suite T over a program P is satisfied iff. the execution of
     * each test case t in T will cause each boolean atom of each branching statement in the code to
     * evaluate at least once to true, and at least once to false.
     * <p>
     * To illustrate this, consider the following:
     * <p>
     * <code>
     * public boolean isOrdered(int a, int b, int c, int d) {
     * <br>if(a < b && b < c && c < d) 
     * <br>return a; 
     * <br>else 
     * <br>return b;
     * <br>}
     * </code>
     * <p>
     * In the above, we have a single branching condition, which is the if-statement. The conditions
     * in this code is the set of atomic boolean sub-expressions inside this branching condition,
     * such that there exist no other boolean subexpressions within it. In our case, the only such
     * subconditions are <code>a < b</code>, <code>b < c</code>, <code>c < d</code>. Thus in order
     * to satisfy Condition Coverage for this snippet, we will need to provide sufficient testcases,
     * such that each of these conditions evaluate at least once to true, and at least one to false.
     * need to provide testcases s.t. this will once evaluate to true (i.e. a >= b) and at least
     * once to false (i.e. a < b).
     * <p>
     * NOTE: It should be remembered that, for larger programs, combinatorial explosion can easily
     * occur when Condition Coverage is pursued. Even in our simple example above, assuming a
     * worst-case scenario, we would need 2^3 test cases in order to satsify Condition Coverage.
     * This number can of course grow rapidly with more complex methods.
     * 
     * @param root
     *            the root of the symbolic execution tree
     * @return
     */
    public List<IExecutionNode> getConditionCoveringNodes(IExecutionStartNode root) {

        throw new UnsupportedOperationException("Not implemented yet");
    }
}
