package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.Node;
import org.jgrapht.graph.DefaultEdge;

import java.util.Objects;

public class AnnotatedEdge extends DefaultEdge {
    public final transient Node proofStep;
    public final boolean consumesInput;
    private final int serialNr;

    public AnnotatedEdge(Node proofStep, boolean consumesInput, int serialNr) {
        this.proofStep = proofStep;
        this.consumesInput = consumesInput;
        this.serialNr = serialNr;
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

        if (consumesInput != that.consumesInput || serialNr != that.serialNr) {
            return false;
        }
        return proofStep.equals(that.proofStep);
    }

    @Override
    public int hashCode() {
        int result = Objects.hash(proofStep, serialNr);
        result = 31 * result + (consumesInput ? 1 : 0);
        return result;
    }
}
