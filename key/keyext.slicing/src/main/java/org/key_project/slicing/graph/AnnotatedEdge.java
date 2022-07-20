package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.Node;
import org.jgrapht.graph.DefaultEdge;

public class AnnotatedEdge extends DefaultEdge {
    public final transient Node proofStep;
    public final boolean consumesInput;

    public AnnotatedEdge(Node proofStep, boolean consumesInput) {
        this.proofStep = proofStep;
        this.consumesInput = consumesInput;
    }
}
