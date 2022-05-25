package org.key_project.slicing.graph;

public class PseudoOutput implements GraphNode {
    @Override
    public String toString(boolean abbreviated) {
        return "pseudo output " + Integer.toHexString(hashCode());
    }
}
