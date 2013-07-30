package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;

public class PathCoverageParser implements ICodeCoverageParser {

    private static final PathCoverageBuilder builder = PathCoverageBuilder.getInstance();

    /**
     * <p>
     * Returns a set of {@link IExecutionNode} instances, s.t. generating a test
     * case covering each of these nodes will satisfy Path Coverage for this
     * symbolic execution tree.
     * </p>
     * <p>
     * Path Coverage for a test suite T over a program P is satisfied iff. the
     * execution of each test case t in T will cause each feasible execution
     * path throughout the tree to be taken at least once.
     * </p>
     * <p>
     * NOTE: Path coverage is not feasible to obtain for many programs.
     * Furthermore, for programs involving loops, full path coverage is usually
     * impossible to achieve, since the symbolic representation of a loop
     * sequence results in an infinite number of possible execution paths. In
     * that event, this method returns <code>null</code>.
     * </p>
     * 
     * @param root
     *            the root of the symbolic execution tree
     * @return
     */
    @Override
    public List<IExecutionNode> retrieveNodes(final IExecutionStart root) {

        final ExecutionPathContext context = ExecutionPathContext.constructExecutionContext(root);

        final Set<ExecutionPath> executionPaths = PathCoverageParser.builder.retrieveExecutionPaths(context);
        final List<IExecutionNode> resultNodes = new LinkedList<IExecutionNode>();
        for (final ExecutionPath path : executionPaths) {
            resultNodes.add(path.getTerminatingNode());
        }
        return resultNodes;
    }
}
