package org.key_project.slicing;

import java.util.List;

public class DependencyNodeData {
    public final List<GraphNode> inputs;
    public final List<GraphNode> outputs;
    public final String label;

    public DependencyNodeData(List<GraphNode> inputs, List<GraphNode> outputs, String label) {
        this.inputs = inputs;
        this.outputs = outputs;
        this.label = label;
    }
}
