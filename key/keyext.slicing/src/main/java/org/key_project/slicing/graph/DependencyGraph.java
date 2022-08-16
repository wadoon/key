package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import org.jgrapht.Graph;
import org.jgrapht.graph.DirectedMultigraph;
import org.jgrapht.traverse.BreadthFirstIterator;
import org.key_project.slicing.DependencyNodeData;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.stream.Stream;

/**
 * This dependency graph tracks the flow of rule applications in the proof tree.
 * Formulas (plus their branch location and sequent location) correspond to nodes.
 * Rule applications correspond to edges.
 * Note that the direction of edges is as follows: inputs/assumptions --(rule app)--> outputs
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
     * Mapping of rule applications to graph edges.
     */
    private final Map<Node, Collection<AnnotatedEdge>> edgeDataReversed = new IdentityHashMap<>();

    private final Map<GraphNode, GraphNode> nodeToNode = new HashMap<>();

    /**
     * Add a rule application to the dependency graph.
     *
     * @param node the node to add
     * @param input inputs required by this proof step
     *              (pairs of graph node + whether the rule app consumes the node)
     * @param output outputs produced by this proof step
     */
    public void addRuleApplication(Node node, Collection<Pair<GraphNode, Boolean>> input, Collection<GraphNode> output) {
        var i = 0;
        for (var in : input) {
            for (var out : output) {
                if (!nodeToNode.containsKey(in.first)) {
                    graph.addVertex(in.first);
                    nodeToNode.put(in.first, in.first);
                } else {
                    in = new Pair<>(nodeToNode.get(in.first), in.second);
                }
                if (!nodeToNode.containsKey(out)) {
                    graph.addVertex(out);
                    nodeToNode.put(out, out);
                } else {
                    out = nodeToNode.get(out);
                }
                var edge = new AnnotatedEdge(node, in.second, i);
                i++;
                graph.addEdge(in.first, out, edge);
                edgeData.put(edge, node);
                edgeDataReversed.computeIfAbsent(node, n -> new ArrayList<>()).add(edge);
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

    public Stream<GraphNode> nodesInBranch(BranchLocation location) {
        return graph.vertexSet().stream()
                .filter(it -> it.branchLocation.hasPrefix(location));
    }

    public Stream<ClosedGoal> goalsInBranch(BranchLocation location) {
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

    /**
     * Gets all the edges representing the supplied proof step.
     * May be used to reconstruct the hyperedge corresponding to the proof step.
     *
     * @param proofStep the proof step
     * @return the edges representing this step
     */
    public Collection<AnnotatedEdge> edgesOf(Node proofStep) {
        return edgeDataReversed.get(proofStep);
    }

    /**
     * @param edge a graph edge
     * @return source node of this edge
     */
    public GraphNode inputOf(AnnotatedEdge edge) {
        return graph.getEdgeSource(edge);
    }

    /**
     * @param edge a graph edge
     * @return target node of this edge
     */
    public GraphNode outputOf(AnnotatedEdge edge) {
        return graph.getEdgeTarget(edge);
    }

    public Stream<GraphNode> inputsOf(Node proofStep) {
        return edgesOf(proofStep).stream().map(this::inputOf);
    }

    public Stream<GraphNode> outputsOf(Node proofStep) {
        return edgesOf(proofStep).stream().map(this::outputOf);
    }

    public Stream<GraphNode> inputsConsumedBy(Node proofStep) {
        return edgesOf(proofStep).stream().filter(edge -> edge.consumesInput).map(this::inputOf);
    }

    public Stream<AnnotatedEdge> edgesUsing(GraphNode node) {
        return outgoingGraphEdgesOf(node).map(it -> it.third);
    }

    public Stream<AnnotatedEdge> edgesConsuming(GraphNode node) {
        return outgoingGraphEdgesOf(node)
                .filter(it -> it.third.consumesInput)
                .map(it -> it.third);
    }

    public int countNodes() {
        return graph.vertexSet().size();
    }

    public int countEdges() {
        return graph.edgeSet().size();
    }
}
