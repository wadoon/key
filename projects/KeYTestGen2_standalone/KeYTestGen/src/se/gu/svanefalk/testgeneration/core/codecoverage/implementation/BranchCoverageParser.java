package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

public class BranchCoverageParser implements ICodeCoverageParser {

    private static final BranchCoverageBuilder builder = BranchCoverageBuilder.getInstance();

    /**
     * <p>
     * Returns a set of {@link IExecutionNode} instances, s.t. generating a test
     * case covering each of these nodes will satisfy Branch Coverage for this
     * symbolic execution tree.
     * </p>
     * <p>
     * Branch Coverage for a test suite T over a program P is satisfied iff. the
     * execution of each test case t in T will cause each possible path between
     * two statement in P to be taken at least once.
     * </p>
     * 
     * @param root
     *            the root of the symbolic execution tree
     * @return
     */
    @Override
    public List<IExecutionNode> retrieveNodes(final IExecutionStartNode root) {

        final ExecutionPathContext context = ExecutionPathContext.constructExecutionContext(root);

        final Set<ExecutionPath> executionPaths = BranchCoverageParser.builder.retrieveExecutionPaths(context);
        final List<IExecutionNode> resultNodes = new LinkedList<IExecutionNode>();
        for (final ExecutionPath path : executionPaths) {
            resultNodes.add(path.getTerminatingNode());
        }
        return resultNodes;
    }
}
