package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.BranchLocation;

/**
 * Graph node used if a rule application did not use any input formulas.
 * This is required to ensure that all rule application are present in the graph.
 *
 * @author Arne Keller
 */
public class PseudoInput extends GraphNode {
    public PseudoInput() {
        super(BranchLocation.root()); // branch location of pseudo outputs does not matter
    }

    @Override
    public String toString(boolean abbreviated, boolean omitBranch) {
        return "pseudo input " + Integer.toHexString(hashCode());
    }
}
