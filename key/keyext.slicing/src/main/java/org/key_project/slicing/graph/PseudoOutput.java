package org.key_project.slicing.graph;

import org.key_project.util.collection.ImmutableSLList;

/**
 * Graph node used if a rule application did not produce any outputs.
 * This is required to ensure that all rule application are present in the graph.
 *
 * @author Arne Keller
 */
public class PseudoOutput extends GraphNode {
    public PseudoOutput() {
        super(ImmutableSLList.nil()); // TODO
    }

    @Override
    public String toString(boolean abbreviated, boolean omitBranch) {
        return "pseudo output " + Integer.toHexString(hashCode());
    }
}
