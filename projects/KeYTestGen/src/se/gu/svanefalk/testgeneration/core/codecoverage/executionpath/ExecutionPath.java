package se.gu.svanefalk.testgeneration.core.codecoverage.executionpath;

import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

public class ExecutionPath {

    private List<PathNode> coveredNodes;
    private IExecutionNode terminatingNode;

    public ExecutionPath() {
        // TODO Auto-generated constructor stub
    }

    public ExecutionPath(final List<PathNode> coveredNodes,
            final IExecutionNode terminatingNode) {
        super();
        this.coveredNodes = coveredNodes;
        this.terminatingNode = terminatingNode;
    }

    /**
     * @return the coveredNodes
     */
    public List<PathNode> getCoveredNodes() {
        return this.coveredNodes;
    }

    /**
     * @return the terminatingNode
     */
    public IExecutionNode getTerminatingNode() {
        return this.terminatingNode;
    }

    /**
     * @param coveredNodes
     *            the coveredNodes to set
     */
    public void setCoveredNodes(final List<PathNode> coveredNodes) {
        this.coveredNodes = coveredNodes;
    }

    /**
     * @param terminatingNode
     *            the terminatingNode to set
     */
    public void setTerminatingNode(final IExecutionNode terminatingNode) {
        this.terminatingNode = terminatingNode;
    }

    @Override
    public String toString() {

        final StringBuilder toPrint = new StringBuilder();
        final Iterator<PathNode> iterator = this.coveredNodes.iterator();
        while (iterator.hasNext()) {
            toPrint.append(iterator.next());

            if (iterator.hasNext()) {
                toPrint.append(" --> \n");
            }
        }

        return toPrint.toString();
    }
}
