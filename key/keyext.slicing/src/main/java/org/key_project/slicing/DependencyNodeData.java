package org.key_project.slicing;

import java.util.List;

public class DependencyNodeData {
    public List<GraphNode> inputs;
    public List<TrackedFormula> outputs;
    public List<String> closedGoals;
    public String label;

    public DependencyNodeData(List<GraphNode> inputs, List<TrackedFormula> outputs, List<String> closedGoals, String label) {
        this.inputs = inputs;
        this.outputs = outputs;
        this.closedGoals = closedGoals;
        this.label = label;
    }
}
