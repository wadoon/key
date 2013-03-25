package se.gu.svanefalk.testgeneration.core.codecoverage.pathcontext;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;

/**
 * Constructs instances of {@link PathNode}
 * 
 * @author christopher
 * 
 */
public enum PathNodeFactory {
    INSTANCE;

    public <T extends PathNode> T constructExecutionNode(
            final IExecutionNode node) {

        if (node instanceof IExecutionTermination) {
            return (T) new PathTerminatingNode();
        }

        if (node instanceof IExecutionBranchCondition) {
            return (T) new PathBranchNode();
        }

        if (node instanceof IExecutionBranchNode) {
            return (T) new PathBranchNode();
        }

        if (node instanceof IExecutionStatement) {
            return (T) new PathStatementNode();
        }

        if (node.getClass() == IExecutionStartNode.class) {
            return (T) new PathStatementNode();
        }

        return null;
    }
}