package de.uka.ilkd.key.testgeneration.core.codecoverage.implementation;

import java.util.List;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.testgeneration.core.codecoverage.ICodeCoverageParser;

public class DecisionCoverageParser implements ICodeCoverageParser {

    /**
     * <p>
     * Returns a set of {@link IExecutionNode} instances, s.t. generating a test
     * case covering each of these nodes will satisfy Decision Coverage for this
     * symbolic execution tree.
     * </p>
     * <p>
     * Decision Coverage for a test suite T over a program P is satisfied iff.
     * the execution of each test case t in T will cause each branching
     * statement in the code (such as if...else statements and the like) to
     * evaluate at least once to true, and at least once to false.
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
     * In the above, our only branching condition is the condition in the
     * if-statement, <code>a >= b</code>. Accordingly, we need to provide
     * testcases s.t. this will once evaluate to true (i.e. a >= b) and at least
     * once to false (i.e. a < b).
     * 
     * @param root
     *            the root of the symbolic execution tree
     * @return
     */
    @Override
    public List<IExecutionNode> retrieveNodes(final IExecutionStartNode root) {

        throw new UnsupportedOperationException("Not implemented yet");
    }
}
