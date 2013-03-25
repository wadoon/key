package se.gu.svanefalk.testgeneration.core.codecoverage.pathcontext;

import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

public class ExecutionPath {

    private final List<PathNode> coveredNodes;

    public ExecutionPath(final List<PathNode> coveredNodes,
            final IExecutionNode terminatingNode) {
        super();
        this.coveredNodes = coveredNodes;
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
