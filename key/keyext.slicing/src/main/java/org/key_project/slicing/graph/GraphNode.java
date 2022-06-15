package org.key_project.slicing.graph;

import org.key_project.util.collection.ImmutableList;

/**
 * A graph node used in the {@link DependencyGraph}.
 *
 * @author Arne Keller
 */
public abstract class GraphNode {
    /**
     * Location in the proof tree.
     */
    protected final ImmutableList<String> branchLocation; // TODO: introduce a proper class for this?
    protected GraphNode(ImmutableList<String> branchLocation) {
        this.branchLocation = branchLocation;
    }

    /**
     * @return the branch location of this node (empty if not applicable)
     */
    public ImmutableList<String> getBranchLocation() {
        return branchLocation;
    }

    /**
     * Construct a human-friendly representation of this graph node.
     *
     * @param abbreviated whether any text should be abbreviated
     * @return textual representation of this object
     */
    public abstract String toString(boolean abbreviated);
}
