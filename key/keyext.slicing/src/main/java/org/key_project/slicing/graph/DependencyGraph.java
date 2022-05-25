package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedMultigraph;
import org.key_project.slicing.DependencyNodeData;

import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.stream.Stream;

public class DependencyGraph {
    private final Graph<GraphNode, DefaultEdge> graph = new DirectedMultigraph<>(DefaultEdge.class);
    private final Map<DefaultEdge, Node> edgeData = new IdentityHashMap<>();

    public void addRuleApplication(Node node, Collection<GraphNode> input, Collection<GraphNode> output) {
        for (var in : input) {
            for (var out : output) {
                graph.addVertex(in);
                graph.addVertex(out);
                if (graph.containsEdge(in, out)) {
                    continue;
                }
                var edge = new DefaultEdge();
                graph.addEdge(in, out, edge);
                edgeData.put(edge, node);
            }
        }
    }

    public Stream<Node> incomingEdgesOf(GraphNode node) {
        return graph.incomingEdgesOf(node).stream().map(edgeData::get);
    }

    public void prune(ProofTreeEvent e) {
        for (var edge : graph.edgeSet().toArray(new DefaultEdge[0])) {
            var node = edgeData.get(edge);
            if (!e.getSource().find(node) || node.getAppliedRuleApp() == null) {
                var data = node.lookup(DependencyNodeData.class);
                for (var out : data.outputs) {
                    graph.removeVertex(out);
                }
            }
        }
    }
}
