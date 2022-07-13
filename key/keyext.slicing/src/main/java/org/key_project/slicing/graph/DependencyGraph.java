package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import org.jgrapht.Graph;
import org.jgrapht.graph.DirectedMultigraph;
import org.jgrapht.traverse.BreadthFirstIterator;
import org.key_project.slicing.DependencyNodeData;
import org.key_project.util.collection.ImmutableList;

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
    private final Graph<GraphNode, AnnotatedEdge> graph = new DirectedMultigraph<>(AnnotatedEdge.class);
    /**
     * Mapping of graph edges to rule applications.
     * Required to get the proof node corresponding to an edge.
     */
    private final Map<AnnotatedEdge, Node> edgeData = new IdentityHashMap<>();

    /**
     * Add a rule application to the dependency graph.
     *
     * @param node the node to add
     * @param input inputs required by this proof step
     *              (pairs of graph node + whether the rule app consumes the node)
     * @param output outputs produced by this proof step
     */
    public void addRuleApplication(Node node, Collection<Pair<GraphNode, Boolean>> input, Collection<GraphNode> output) {
        for (var in : input) {
            for (var out : output) {
                graph.addVertex(in.first);
                graph.addVertex(out);
                /*
                if (graph.containsEdge(in, out)) {
                    continue;
                }
                 */
                var edge = new AnnotatedEdge(in.second);
                graph.addEdge(in.first, out, edge);
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
     * @return the rule application(s) that produced the graph node, if any
     */
    public Stream<Node> incomingEdgesOf(GraphNode node) {
        if (!graph.containsVertex(node)) {
            return Stream.of();
        }
        return graph.incomingEdgesOf(node).stream().map(edgeData::get);
    }

    /**
     * @param node a graph node
     * @return the incoming (graph edges, graph sources) of that node
     */
    public Stream<Triple<Node, GraphNode, AnnotatedEdge>> incomingGraphEdgesOf(GraphNode node) {
        if (!graph.containsVertex(node)) {
            return Stream.of();
        }
        return graph.incomingEdgesOf(node).stream()
                .map(edge -> new Triple<>(edgeData.get(edge), graph.getEdgeSource(edge), edge));
    }

    /**
     * @param node a graph node
     * @return the rule application(s) that used the graph node, if any
     */
    public Stream<Node> outgoingEdgesOf(GraphNode node) {
        if (!graph.containsVertex(node)) {
            return Stream.of();
        }
        return graph.outgoingEdgesOf(node).stream().map(edgeData::get);
    }

    /**
     * @param node a graph node
     * @return the outgoing (graph edges, graph targets) of that node
     */
    public Stream<Triple<Node, GraphNode, AnnotatedEdge>> outgoingGraphEdgesOf(GraphNode node) {
        if (!graph.containsVertex(node)) {
            return Stream.of();
        }
        return graph.outgoingEdgesOf(node).stream()
                .map(edge -> new Triple<>(edgeData.get(edge), graph.getEdgeTarget(edge), edge));
    }

    public Stream<GraphNode> nodesInBranch(ImmutableList<String> location) {
        return graph.vertexSet().stream()
                .filter(it -> it.branchLocation.hasPrefix(location));
    }

    public Stream<ClosedGoal> goalsInBranch(ImmutableList<String> location) {
        return graph.vertexSet().stream()
                .filter(ClosedGoal.class::isInstance)
                .map(ClosedGoal.class::cast)
                .filter(it -> it.branchLocation.hasPrefix(location));
    }

    public BreadthFirstIterator<GraphNode, AnnotatedEdge> breadthFirstIterator(GraphNode start) {
        return new BreadthFirstIterator<>(graph, start);
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
        for (var edge : graph.edgeSet().toArray(new AnnotatedEdge[0])) {
            var node = edgeData.get(edge);
            if (!e.getSource().find(node) || node.getAppliedRuleApp() == null) {
                var data = node.lookup(DependencyNodeData.class);
                for (var out : data.outputs) {
                    graph.removeVertex(out);
                }
            }
        }
    }

    public Stream<GraphNode> neighborsOf(GraphNode node) {
        return Stream.concat(
                graph.incomingEdgesOf(node).stream().map(graph::getEdgeSource),
                graph.outgoingEdgesOf(node).stream().map(graph::getEdgeTarget)
        );
    }
}
