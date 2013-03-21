package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.LinkedList;
import java.util.List;

import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;

import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

public class StatementCoverageParser implements ICodeCoverageParser {

    /**
     * <p>
     * Returns a set of {@link IExecutionNode} instances, s.t. generating a test
     * case covering each of these nodes will satisfy Statement Coverage for
     * this symbolic execution tree.
     * </p>
     * <p>
     * Statement Coverage is satisfied iff. a set of test cases is provided,
     * s.t. the execution of these test cases will lead to each statement in the
     * IUT being executed at least once.
     * </p>
     * 
     * @param root
     *            the root of the symbolic execution tree
     * @return
     */
    @Override
    public List<IExecutionNode> retrieveNodes(final IExecutionStartNode root) {

        /*
         * Due to the way symbolic execution trees are implemented (do not
         * confuse them with standard execution trees), simply gathering all
         * return assertions should guarantee full statement coverage. See
         * separate proof.
         */
        final ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(
                root);
        final List<IExecutionNode> nodes = new LinkedList<IExecutionNode>();

        while (iterator.hasNext()) {
            final IExecutionNode next = iterator.next();
            if (next instanceof IExecutionMethodReturn) {
                nodes.add(next);
            }
        }
        return nodes;
    }
}
