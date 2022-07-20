package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.BranchLocation;

/**
 * Graph node that represents a closed goal.
 *
 * @author Arne Keller
 */
public class ClosedGoal extends GraphNode {
    /**
     * The serial number of the corresponding node in the proof tree.
     *
     * @see de.uka.ilkd.key.proof.Node#serialNr()
     */
    public final int serialNr;

    public ClosedGoal(int serialNr, BranchLocation branchLocation) {
        super(branchLocation);
        this.serialNr = serialNr;
    }

    @Override
    public String toString(boolean abbreviated, boolean omitBranch) {
        return "closed goal " + serialNr;
    }
}
