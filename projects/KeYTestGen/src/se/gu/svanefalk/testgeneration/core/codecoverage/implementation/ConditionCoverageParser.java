package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.List;

import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

public class ConditionCoverageParser implements ICodeCoverageParser {

    /**
     * <p>
     * Returns a set of {@link IExecutionNode} instances, s.t. generating a test
     * case covering each of these nodes will satisfy Condition Coverage for
     * this symbolic execution tree.
     * <p>
     * Condition Coverage for a test suite T over a program P is satisfied iff.
     * the execution of each test case t in T will cause each boolean atom of
     * each branching statement in the code to evaluate at least once to true,
     * and at least once to false.
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
     * In the above, we have a single branching condition, which is the
     * if-statement. The conditions in this code is the set of atomic boolean
     * sub-expressions inside this branching condition, such that there exist no
     * other boolean subexpressions within it. In our case, the only such
     * subconditions are <code>a < b</code>, <code>b < c</code>,
     * <code>c < d</code>. Thusm in order to satisfy Condition Coverage for this
     * snippet, we will need to provide sufficient testcases, such that each of
     * these conditions evaluate at least once to true, and at least one to
     * false. need to provide testcases s.t. this will once evaluate to true
     * (i.e. a >= b) and at least once to false (i.e. a < b).
     * <p>
     * NOTE: It should be remembered that, for larger programs, combinatorial
     * explosion can easily occur when Condition Coverage is pursued. Even in
     * our simple example above, assuming a worst-case scenario, we would need
     * 2^3 test cases in order to satsify Condition Coverage. This number can of
     * course grow rapidly with more complex methods.
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
