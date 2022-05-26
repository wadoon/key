package org.key_project.slicing.graph;

/**
 * Graph node that represents a closed goal.
 *
 * @author Arne Keller
 */
public class ClosedGoal implements GraphNode {
    /**
     * The serial number of the corresponding node in the proof tree.
     *
     * @see de.uka.ilkd.key.proof.Node#serialNr()
     */
    public final int serialNr;

    public ClosedGoal(int serialNr) {
        this.serialNr = serialNr;
    }

    @Override
    public String toString(boolean abbreviated) {
        return "closed goal " + serialNr;
    }
}
