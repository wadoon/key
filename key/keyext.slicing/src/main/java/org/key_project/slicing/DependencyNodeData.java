package org.key_project.slicing;

import java.util.List;

public class DependencyNodeData {
    public List<String> inputs;
    public List<String> outputs;
    public String label;

    public DependencyNodeData(List<String> inputs, List<String> outputs, String label) {
        this.inputs = inputs;
        this.outputs = outputs;
        this.label = label;
    }
}
