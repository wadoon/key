package org.key_project.slicing.graph;

/**
 * Graph node used if a rule application did not produce any outputs.
 * This is required to ensure that all rule application are present in the graph.
 *
 * @author Arne Keller
 */
public class PseudoOutput implements GraphNode {
    @Override
    public String toString(boolean abbreviated) {
        return "pseudo output " + Integer.toHexString(hashCode());
    }
}
