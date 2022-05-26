package org.key_project.slicing.graph;

/**
 * Graph node used if a rule application did not use any input formulas.
 * This is required to ensure that all rule application are present in the graph.
 *
 * @author Arne Keller
 */
public class PseudoInput implements GraphNode {
    @Override
    public String toString(boolean abbreviated) {
        return "pseudo input " + Integer.toHexString(hashCode());
    }
}
