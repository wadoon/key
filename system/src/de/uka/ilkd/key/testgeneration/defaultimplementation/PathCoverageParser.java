package de.uka.ilkd.key.testgeneration.defaultimplementation;

import java.util.List;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.testgeneration.codecoverage.ICodeCoverageParser;

public class PathCoverageParser
        implements ICodeCoverageParser {

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
    @Override
    public List<IExecutionNode> retrieveNodes(IExecutionStartNode root) {

        throw new UnsupportedOperationException("Not implemented yet");
    }
}
