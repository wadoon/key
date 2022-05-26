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

/**
 * This dependency graph tracks the flow of rule applications in the proof tree.
 * Formulas (plus their branch location and sequent location) correspond to nodes.
 * Rule applications correspond to edges.
 *
 * @author Arne Keller
 */
public class DependencyGraph {
    /**
     * Main storage container.
     * Edges start at input formulas and end at formulas produced by the rule application.
     */
    private final Graph<GraphNode, DefaultEdge> graph = new DirectedMultigraph<>(DefaultEdge.class);
    /**
     * Mapping of graph edges to rule applications.
     * Required because we can not add the same edge twice.
     */
    private final Map<DefaultEdge, Node> edgeData = new IdentityHashMap<>();

    /**
     * Add a rule application to the dependency graph.
     *
     * @param node the node to add
     * @param input inputs required by this proof step
     * @param output outputs produced by this proof step
     */
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

    /**
     * @param node a graph node
     * @return whether the graph contains that node
     */
    public boolean containsNode(GraphNode node) {
        return graph.containsVertex(node);
    }

    /**
     * @param node a graph node
     * @return the rule application(s) that produced the graph node
     */
    public Stream<Node> incomingEdgesOf(GraphNode node) {
        return graph.incomingEdgesOf(node).stream().map(edgeData::get);
    }

    /**
     * @return all nodes contained in the graph
     */
    public Iterable<GraphNode> nodes() {
        return graph.vertexSet();
    }

    /**
     * Process a prune of the proof tree.
     * Deletes graph data that belongs to removed steps.
     *
     * @param e the proof slicing event
     */
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
