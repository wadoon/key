package org.key_project.slicing.graph;

/**
 * A graph node used in the {@link DependencyGraph}.
 *
 * @author Arne Keller
 */
public interface GraphNode {
    /**
     * Construct a human-friendly representation of this graph node.
     *
     * @param abbreviated whether any text should be abbreviated
     * @return textual representation of this object
     */
    String toString(boolean abbreviated);
}
