package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.slicing.AnalysisResults;
import org.key_project.slicing.DependencyNodeData;

import java.util.ArrayList;

public final class DotExporter {
    private DotExporter() { }

    public static String exportDot(
            Proof proof,
            DependencyGraph graph,
            AnalysisResults analysisResults,
            boolean abbreviateFormulas
    ) {
        var buf = new StringBuilder();
        buf.append("digraph {\n");
        buf.append("edge [dir=\"back\"];\n");
        var queue = new ArrayList<Node>();
        queue.add(proof.root());
        while (!queue.isEmpty()) {
            var node = queue.remove(queue.size() - 1);
            node.childrenIterator().forEachRemaining(queue::add);
            var data = node.lookup(DependencyNodeData.class);
            if (data == null) {
                continue;
            }
            for (var in : data.inputs) {
                data.outputs.stream().map(it -> it.toString(abbreviateFormulas)).forEach(out -> {
                    buf
                            .append('"')
                            .append(in.toString(abbreviateFormulas))
                            .append("\" -> \"")
                            .append(out)
                            .append("\" [label=\"")
                            .append(data.label);
                    if (analysisResults != null && !analysisResults.usefulSteps.contains(node)) {
                        buf.append("\" color=\"red");
                    }
                    buf
                            .append("\"]\n");
                });
            }
        }
        if (analysisResults != null) {
            for (var formula : graph.nodes()) {
                if (!analysisResults.usefulNodes.contains(formula)) {
                    buf.append('"').append(formula.toString(abbreviateFormulas)).append('"').append(" [color=\"red\"]\n");
                }
            }
        }
        buf.append("}");
        return buf.toString();
    }
}
