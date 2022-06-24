package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Pair;
import org.key_project.slicing.AnalysisResults;
import org.key_project.slicing.DependencyNodeData;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.stream.Stream;

public final class DotExporter {
    private DotExporter() {
    }

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
                data.outputs.stream().map(it -> it.toString(abbreviateFormulas, false)).forEach(out -> {
                    buf
                            .append('"')
                            .append(in.toString(abbreviateFormulas, false))
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
                    buf.append('"').append(formula.toString(abbreviateFormulas, false)).append('"').append(" [color=\"red\"]\n");
                }
            }
        }
        buf.append("}");
        return buf.toString();
    }

    public static String exportDotAround(
            Proof proof,
            DependencyGraph graph,
            AnalysisResults analysisResults,
            boolean abbreviateFormulas,
            boolean omitBranch,
            GraphNode graphNode
    ) {
        var buf = new StringBuilder();
        buf.append("digraph {\n");
        buf.append("edge [dir=\"back\"];\n");
        var queue = new ArrayList<Pair<GraphNode, Integer>>();
        queue.add(new Pair<>(graphNode, 0));
        var visited = new HashSet<GraphNode>();
        var drawn = new HashSet<Node>();
        while (!queue.isEmpty()) {
            var nodePair = queue.remove(queue.size() - 1);
            if (visited.contains(nodePair.first)) {
                continue;
            }
            var nodeB = nodePair.first;
            visited.add(nodeB);
            var incoming = graph.incomingEdgesOf(nodeB);
            var outgoing = graph.outgoingEdgesOf(nodeB);
            Stream.concat(incoming, outgoing).forEach(node -> {
                if (drawn.contains(node)) {
                    return;
                }
                drawn.add(node);
                var data = node.lookup(DependencyNodeData.class);
                if (data == null) {
                    return;
                }
                for (var in : data.inputs) {
                    for (var out : data.outputs) {
                        var inString = in.toString(abbreviateFormulas, omitBranch);
                        var outString = out.toString(abbreviateFormulas, omitBranch);
                        buf
                                .append('"')
                                .append(inString)
                                .append("\" -> \"")
                                .append(outString)
                                .append("\" [label=\"")
                                .append(data.label);
                        if (analysisResults != null && !analysisResults.usefulSteps.contains(node)) {
                            buf.append("\" color=\"red");
                        }
                        buf
                                .append("\"];\n");
                        if (analysisResults != null) {
                            if (!analysisResults.usefulNodes.contains(in)) {
                                buf.append('"').append(inString).append('"').append(" [color=\"red\"]\n");
                            }
                            if (!analysisResults.usefulNodes.contains(out)) {
                                buf.append('"').append(outString).append('"').append(" [color=\"red\"]\n");
                            }
                        }
                    }
                }
            });
            if (nodePair.second < 1) {
                graph.neighborsOf(nodeB).forEach(newNode -> queue.add(new Pair<>(newNode, nodePair.second + 1)));
            }
        }
        buf.append('"').append(graphNode.toString(abbreviateFormulas, omitBranch)).append("\" [fontsize=\"28pt\"];");
        buf.append('}');
        return buf.toString();
    }
}
