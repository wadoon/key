package de.uka.ilkd.key.testgeneration.codecoverage.implementation;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.testgeneration.codecoverage.ICodeCoverageParser;

public class StatementCoverageParser
        implements ICodeCoverageParser {

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
    @Override
    public List<IExecutionNode> retrieveNodes(IExecutionStartNode root) {

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
}
