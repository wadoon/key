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
import java.util.stream.Collectors;

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
            if (!usefulSteps.contains(node) || node.childrenCount() <= 1) {
                return;
            }
            var data = node.lookup(DependencyNodeData.class);
            var groupedOutputs = data.outputs
                    .stream().collect(Collectors.groupingBy(GraphNode::branch));
            var cutWasUseful = groupedOutputs.values().stream()
                    .allMatch(l -> l.stream().anyMatch(usefulFormulas::contains));
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
            // TODO: mark inputs as useless, if possible
            // TODO: process newly useless nodes somehow (-> to mark more edges as useless..)
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
        var rules = new RuleStatistics();
        proof.breadthFirstSearch(proof.root(), (theProof, node) -> {
            if (node.getAppliedRuleApp() == null) {
                return;
            }
            var branches = node.childrenCount() > 1;
            var rule = node.getAppliedRuleApp().rule();
            if (usefulSteps.contains(node)) {
                rules.addApplication(rule, branches);
            } else {
                if (node.lookup(DependencyNodeData.class)
                        .inputs.stream().anyMatch(usefulFormulas::contains)) {
                    rules.addInitialUselessApplication(rule, branches);
                } else {
                    rules.addUselessApplication(rule, branches);
                }
            }
        });

        return new AnalysisResults(steps, usefulSteps.size(), rules, usefulSteps, usefulFormulas);
    }
}
