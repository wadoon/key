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

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        AnnotatedEdge that = (AnnotatedEdge) o;

        if (consumesInput != that.consumesInput) {
            return false;
        }
        return proofStep.equals(that.proofStep);
    }

    @Override
    public int hashCode() {
        int result = proofStep.hashCode();
        result = 31 * result + (consumesInput ? 1 : 0);
        return result;
    }
}
