package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.BranchLocation;

/**
 * Graph node used if a rule application did not produce any outputs.
 * This is required to ensure that all rule application are present in the graph.
 *
 * @author Arne Keller
 */
public class PseudoOutput extends GraphNode {
    public PseudoOutput() {
        super(BranchLocation.root()); // branch location of pseudo outputs does not matter
    }

    @Override
    public String toString(boolean abbreviated, boolean omitBranch) {
        return "pseudo output " + Integer.toHexString(hashCode());
    }
}
