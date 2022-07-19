package org.key_project.slicing;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import org.key_project.slicing.graph.ClosedGoal;
import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.graph.TrackedFormula;
import org.key_project.util.collection.ImmutableList;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
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
        /*
        for (var e : proof.closedGoals()) {
            queue.add(e.node());
        }

        while (!queue.isEmpty()) {
            var node = queue.pop();
            // closed goal & has previous step
            // => mark output (closed goal) of parent node as useful
            var considerOutputs = false;
            if (node.getAppliedRuleApp() == null && node.parent() != null) {
                node = node.parent();
                considerOutputs = true;
            }
            if (usefulSteps.contains(node)) {
                continue;
            }
            usefulSteps.add(node);
            var data = node.lookup(DependencyNodeData.class);
            data.inputs.forEach(it -> usefulFormulas.add(it.first));

            for (var in : data.inputs) {
                graph.incomingEdgesOf(in.first).forEach(queue::add);
            }
            if (considerOutputs) {
                data.outputs.stream().filter(ClosedGoal.class::isInstance).forEach(usefulFormulas::add);
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
        */

        // mark everything as 'useful' to evaluate the second algorithm in isolation
        proof.breadthFirstSearch(proof.root(), ((proof1, visitedNode) -> {
            if (visitedNode.getAppliedRuleApp() == null) {
                return;
            }
            usefulSteps.add(visitedNode);
            var data = visitedNode.lookup(DependencyNodeData.class);
            if (data == null) {
                return;
            }
            data.inputs.stream().map(it -> it.first).forEach(usefulFormulas::add);
            usefulFormulas.addAll(data.outputs);
        }));

        var branchStacks = new HashMap<Node, List<Node>>();
        var foundDuplicates = new HashSet<String>();
        // search for duplicate rule applications
        graph.nodes().forEach(node -> {
            var foundDupes = new HashMap<Triple<RuleApp, SequentFormula, Boolean>, List<Node>>();
            graph.outgoingGraphEdgesOf(node).forEach(t -> {
                var proofNode = t.first;
                if (proofNode.childrenCount() > 1) {
                    return; // do not deduplicate branching steps
                }
                if (!usefulSteps.contains(proofNode)) {
                    return; // do not deduplicate steps that will be sliced away anyway
                }
                var produced = t.second;
                if (!(produced instanceof TrackedFormula)) {
                    return; // do not try to deduplicate the addition of new rules
                }
                var formula = (TrackedFormula) produced;
                foundDupes.computeIfAbsent(new Triple<>(proofNode.getAppliedRuleApp(), formula.formula, formula.inAntec), _a -> new ArrayList<>())
                        .add(proofNode);
            });
            for (var entry : foundDupes.entrySet()) {
                var steps = entry.getValue();
                if (steps.size() > 1) {
                    LOGGER.info("input {} found duplicate {}", node.toString(true, false), Arrays.toString(steps.stream().map(Node::serialNr).toArray()));
                    LOGGER.info(" rule names {}", Arrays.toString(steps.stream().map(x -> x.getAppliedRuleApp().rule().displayName()).toArray()));
                    foundDuplicates.add(steps.get(0).getAppliedRuleApp().rule().displayName());
                    var branchSerial = 0;
                    var prefixes = new ArrayList<ImmutableList<String>>();
                    for (var step : steps) {
                        var commonPrefix = step.branchLocation().stripPrefix(node.getBranchLocation());
                        LOGGER.info("one common prefix {}", Arrays.toString(commonPrefix.toList().toArray()));
                        prefixes.add(commonPrefix);
                    }
                    while (true) {
                        var allSame = true;
                        for (int i = 1; i < prefixes.size(); i++) {
                            if (!prefixes.get(0).head().equals(prefixes.get(i).head())) {
                                allSame = false;
                                break;
                            }
                        }
                        if (!allSame) {
                            break;
                        }
                        prefixes.replaceAll(ImmutableList::tail);
                    }
                    LOGGER.info("differing suffix {}", Arrays.toString(prefixes.get(0).toList().toArray()));
                    branchSerial = Integer.parseInt(prefixes.get(0).head().substring(1).split("_")[0]);
                    final Node[] branchNode = {null};
                    int finalBranchSerial = branchSerial;
                    proof.breadthFirstSearch(proof.root(), (proof1, visitedNode) -> {
                        if (branchNode[0] != null) {
                            return;
                        }
                        if (visitedNode.serialNr() == finalBranchSerial) {
                            branchNode[0] = visitedNode;
                        }
                    });
                    LOGGER.info("branching node {}", branchNode[0].serialNr());
                    steps.stream().skip(1).forEach(usefulSteps::remove);
                    branchStacks.computeIfAbsent(branchNode[0], _node -> new ArrayList<>()).add(steps.get(0));
                }
            }
        });
        for (var x : foundDuplicates) {
            LOGGER.info("rule {}", x);
        }


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
                        .inputs.stream().map(it -> it.first).anyMatch(usefulFormulas::contains)) {
                    rules.addInitialUselessApplication(rule, branches);
                } else {
                    rules.addUselessApplication(rule, branches);
                }
            }
        });

        return new AnalysisResults(proof, steps, usefulSteps.size(), rules, usefulSteps, usefulFormulas, uselessBranches, Map.of()); // branchStacks
    }
}
