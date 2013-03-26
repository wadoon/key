package se.gu.svanefalk.testgeneration.core.codecoverage.executionpath;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Instances of this class represent nodes in an {@link ExecutionGraph}.
 * <p>
 * Instances of this class are essentially high-level abstractions of
 * {@link IExecutionNode} instances, removing the symbolic execution data in
 * order to retain interesting information about the non-symbolic execution of
 * the code under test.
 * 
 * @author christopher
 * 
 */
public abstract class PathNode {

    public static PathNode createNode() {
        return null;
    }

    List<IExecutionNode> correspondingSymbolicNodes = new LinkedList<IExecutionNode>();

    void addCorrespondingSymbolicNode(final IExecutionNode node) {
        this.correspondingSymbolicNodes.add(node);
    }

    public List<IExecutionNode> getCorrespondingSymbolicNodes() {
        return this.correspondingSymbolicNodes;
    }

    @Override
    public String toString() {
        /*
         * There will always be at least one symbolic node associated with this
         * node.
         */
        try {
            return this.correspondingSymbolicNodes.get(0).getName();
        } catch (final ProofInputException e) {
            return "Could not retrieve name of symbolic node";
        }
    }
}