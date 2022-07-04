package org.key_project.slicing;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.util.Triple;
import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.graph.TrackedFormula;
import org.key_project.util.collection.ImmutableList;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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
    private static final Logger LOGGER = LoggerFactory.getLogger(DependencyAnalyzer.class);

    private DependencyAnalyzer() {
    }

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
        var uselessBranches = new HashSet<ImmutableList<String>>();

        // BFS, starting from all closed goals
        var queue = new ArrayDeque<Node>();
        for (var e : proof.closedGoals()) {
            queue.add(e.node());
        }

        while (!queue.isEmpty()) {
            var node = queue.pop();
            // closed goal & has previous step
            if (node.getAppliedRuleApp() == null && node.parent() != null) {
                node = node.parent();
            }
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
            if ((!usefulSteps.contains(node) && false) || node.childrenCount() <= 1) {
                return;
            }
            var data = node.lookup(DependencyNodeData.class);
            var groupedOutputs = data.outputs
                    .stream().collect(Collectors.groupingBy(GraphNode::getBranchLocation));
            var cutWasUseful = groupedOutputs.values().stream()
                    .allMatch(l -> l.stream().anyMatch(usefulFormulas::contains));
            if (cutWasUseful) {
                return;
            }
            usefulSteps.remove(node);
            var completelyUseless = data.outputs.stream().noneMatch(usefulFormulas::contains);
            var counter = node.childrenCount() - 1;
            // mark sub-proof as useless, if necessary
            for (var output : data.outputs) {
                if (!usefulFormulas.contains(output) && !completelyUseless) {
                    continue;
                }
                // TODO: pick the "smallest" sub-proof
                if (completelyUseless && counter == 0) {
                    continue;
                }
                if (completelyUseless) {
                    counter--;
                }
                var formula = (TrackedFormula) output;
                graph.nodesInBranch(formula.getBranchLocation()).forEach(theNode -> {
                    usefulFormulas.remove(theNode);
                    graph.outgoingEdgesOf(theNode).forEach(step -> {
                        usefulSteps.remove(step);
                        step.getNodeInfo().setNotes("useless");
                    });
                });
                uselessBranches.add(formula.getBranchLocation());
            }
            // TODO: mark inputs as useless, if possible
            // TODO: process newly useless nodes somehow (-> to mark more edges as useless..)
        });
        var time1 = System.currentTimeMillis();
        // unmark all 'useful' steps in useless branches
        proof.breadthFirstSearch(proof.root(), (proof1, node) -> {
            if (!usefulSteps.contains(node)) {
                return;
            }
            for (var prefix : uselessBranches) {
                if (node.branchLocation().hasPrefix(prefix)) {
                    usefulSteps.remove(node);
                    node.getNodeInfo().setNotes("useless");
                    return;
                }
            }
        });
        LOGGER.info("last step took {} ms", System.currentTimeMillis() - time1);


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

        var steps = proof.countNodes() - proof.closedGoals().size()
                + (int) proof.closedGoals()
                .stream().filter(it -> it.node().getAppliedRuleApp() instanceof RuleAppSMT).count();

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

        return new AnalysisResults(steps, usefulSteps.size(), rules, usefulSteps, usefulFormulas, uselessBranches);
    }
}
