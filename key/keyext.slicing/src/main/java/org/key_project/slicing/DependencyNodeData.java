package org.key_project.slicing;

import java.util.List;

public class DependencyNodeData {
    public final List<GraphNode> inputs;
    public final List<TrackedFormula> outputs;
    public final List<String> closedGoals;
    public final String label;

    public DependencyNodeData(List<GraphNode> inputs, List<TrackedFormula> outputs, List<String> closedGoals, String label) {
        this.inputs = inputs;
        this.outputs = outputs;
        this.closedGoals = closedGoals;
        this.label = label;
    }
}
