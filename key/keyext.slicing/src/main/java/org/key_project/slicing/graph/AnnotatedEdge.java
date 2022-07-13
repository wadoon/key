package org.key_project.slicing.graph;

import org.jgrapht.graph.DefaultEdge;

public class AnnotatedEdge extends DefaultEdge {
    public final boolean consumesInput;

    public AnnotatedEdge(boolean consumesInput) {
        this.consumesInput = consumesInput;
    }
}
