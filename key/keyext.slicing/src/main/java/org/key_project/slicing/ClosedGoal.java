package org.key_project.slicing;

public class ClosedGoal implements GraphNode {
    public final int serialNr;

    public ClosedGoal(int serialNr) {
        this.serialNr = serialNr;
    }

    public String toString(boolean abbreviated) {
        return "closed goal " + serialNr;
    }
}
