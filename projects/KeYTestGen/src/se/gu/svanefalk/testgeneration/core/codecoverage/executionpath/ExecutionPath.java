package se.gu.svanefalk.testgeneration.core.codecoverage.executionpath;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

public class ExecutionPath {

    private Map<SourceElement, List<IExecutionBranchCondition>> branchConditionMappings;
    private Set<SourceElement> coveredNodes;

    private IExecutionNode terminatingNode;

    public ExecutionPath() {
        // TODO Auto-generated constructor stub
    }

    public ExecutionPath(final Set<SourceElement> coveredNodes,
            final IExecutionNode terminatingNode) {
        super();
        this.coveredNodes = coveredNodes;
        this.terminatingNode = terminatingNode;
    }

    /**
     * @return the branchConditionMappings
     */
    public Map<SourceElement, List<IExecutionBranchCondition>> getBranchConditionMappings() {
        return branchConditionMappings;
    }

    /**
     * @return the coveredNodes
     */
    public Set<SourceElement> getCoveredNodes() {
        return coveredNodes;
    }

    /**
     * @return the terminatingNode
     */
    public IExecutionNode getTerminatingNode() {
        return terminatingNode;
    }

    /**
     * @param branchConditionMappings
     *            the branchConditionMappings to set
     */
    void setBranchConditionMappings(
            final Map<SourceElement, List<IExecutionBranchCondition>> branchConditionMappings) {
        this.branchConditionMappings = branchConditionMappings;
    }

    /**
     * @param coveredNodes
     *            the coveredNodes to set
     */
    public void setCoveredNodes(final Set<SourceElement> coveredNodes) {
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
        final Iterator<SourceElement> iterator = coveredNodes.iterator();
        while (iterator.hasNext()) {
            toPrint.append(iterator.next());

            if (iterator.hasNext()) {
                toPrint.append(" --> ");
            }
        }

        return toPrint.toString();
    }
}
