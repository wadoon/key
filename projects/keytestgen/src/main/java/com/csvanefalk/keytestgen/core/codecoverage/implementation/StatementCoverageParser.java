package com.csvanefalk.keytestgen.core.codecoverage.implementation;

import com.csvanefalk.keytestgen.core.codecoverage.ICodeCoverageParser;
import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPath;
import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPathContext;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class StatementCoverageParser implements ICodeCoverageParser {

    private static final StatementCoverageBuilder builder = StatementCoverageBuilder.getInstance();

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
     * @param root the root of the symbolic execution tree
     * @return
     */
    @Override
    public List<IExecutionNode> retrieveNodes(final IExecutionStart root) {

        final ExecutionPathContext context = ExecutionPathContext.constructExecutionContext(root);

        final Set<ExecutionPath> executionPaths = StatementCoverageParser.builder.retrieveExecutionPaths(context);
        final List<IExecutionNode> resultNodes = new LinkedList<IExecutionNode>();
        for (ExecutionPath path : executionPaths) {
            resultNodes.add(path.getTerminatingNode());
        }
        return resultNodes;
    }
}