package org.key_project.slicing;

import de.uka.ilkd.key.util.Pair;
import org.key_project.slicing.graph.GraphNode;

import java.util.Collections;
import java.util.List;

public class DependencyNodeData {
    public final List<Pair<GraphNode, Boolean>> inputs;
    public final List<GraphNode> outputs;
    public final String label;

    public DependencyNodeData(List<Pair<GraphNode, Boolean>> inputs, List<GraphNode> outputs, String label) {
        this.inputs = Collections.unmodifiableList(inputs);
        this.outputs = Collections.unmodifiableList(outputs);
        this.label = label;
    }
}
