package org.key_project.slicing;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.Triple;
import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.graph.TrackedFormula;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;

/**
 * Implementation of the dependency analysis algorithm.
 *
 * @author Arne Keller
 */
public final class DependencyAnalyzer {
    private DependencyAnalyzer() { }

    public static AnalysisResults analyze(Proof proof, DependencyGraph graph) {
        if (GeneralSettings.noPruningClosed) {
            throw new IllegalStateException("cannot analyze proof with no (recorded) closed goals, "
                    + "try disabling GeneralSettings.noPruningClosed");
        }
        if (proof == null || !proof.closed()) {
            return null;
        }
        var usefulSteps = new HashSet<Node>();
        var usefulFormulas = new HashSet<GraphNode>();

        // BFS, starting from all closed goals
        var queue = new ArrayDeque<Node>();
        for (var e : proof.closedGoals()) {
            queue.add(e.node().parent());
        }

        while (!queue.isEmpty()) {
            var node = queue.pop();
            if (usefulSteps.contains(node)) {
                continue;
            }
            usefulSteps.add(node);
            var data = node.lookup(DependencyNodeData.class);
            usefulFormulas.addAll(data.inputs);

            for (var in : data.inputs) {
                graph.incomingEdgesOf(in).forEach(queue::add);
            }
        }

        // analyze cuts: they are only useful if all of their outputs were used
        proof.breadthFirstSearch(proof.root(), (proof1, node) -> {
            if (!usefulSteps.contains(node)) {
                return;
            }
            var displayName = node.getAppliedRuleApp().rule().displayName();
            if (!displayName.equals("cut")) { // TODO: cut_direct?
                return;
            }
            var data = node.lookup(DependencyNodeData.class);
            var cutWasUseful = usefulFormulas.containsAll(data.outputs);
            if (cutWasUseful) {
                return;
            }
            usefulSteps.remove(node);
            // mark sub-proof as useless, if necessary
            for (var output : data.outputs) {
                if (!usefulFormulas.contains(output)) {
                    continue;
                }
                var formula = (TrackedFormula) output;
                graph.nodesInBranch(formula.branchLocation).forEach(theNode -> {
                    usefulFormulas.remove(theNode);
                    graph.outgoingEdgesOf(theNode).forEach(usefulSteps::remove);
                });
            }
        });

        // add a note to each useless proof step to allow easy identification by the user
        // TODO: make this configurable / add a different indicator?
        queue.add(proof.root());
        while (!queue.isEmpty()) {
            var node = queue.pop();
            if (!usefulSteps.contains(node) && node.getNodeInfo().getNotes() == null) {
                node.getNodeInfo().setNotes("useless");
            }
            node.childrenIterator().forEachRemaining(queue::add);
        }

        var steps = proof.countNodes() - proof.closedGoals().size();

        // gather statistics on useful/useless rules
        var rules = new HashMap<String, Triple<Integer, Integer, Integer>>();
        proof.breadthFirstSearch(proof.root(), (theProof, node) -> {
            if (node.getAppliedRuleApp() == null) {
                return;
            }
            var displayName = node.getAppliedRuleApp().rule().displayName();
            if (!rules.containsKey(displayName)) {
                rules.put(displayName, new Triple<>(0, 0, 0));
            }
            var triple = rules.get(displayName);
            var d2 = !usefulSteps.contains(node) ? 1 : 0;
            var d3 = d2 == 1 && node.lookup(DependencyNodeData.class)
                    .inputs.stream().anyMatch(usefulFormulas::contains) ? 1 : 0;
            rules.put(displayName, new Triple<>(
                    triple.first + 1, triple.second + d2, triple.third + d3));
        });

        return new AnalysisResults(steps, usefulSteps.size(), rules, usefulSteps, usefulFormulas);
    }
}
