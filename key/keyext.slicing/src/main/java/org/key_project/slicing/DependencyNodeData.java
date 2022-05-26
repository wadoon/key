package org.key_project.slicing;

import org.key_project.slicing.graph.GraphNode;

import java.util.Collections;
import java.util.List;

public class DependencyNodeData {
    public final List<GraphNode> inputs;
    public final List<GraphNode> outputs;
    public final String label;

    public DependencyNodeData(List<GraphNode> inputs, List<GraphNode> outputs, String label) {
        this.inputs = Collections.unmodifiableList(inputs);
        this.outputs = Collections.unmodifiableList(outputs);
        this.label = label;
    }
}
