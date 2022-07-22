package org.key_project.slicing;

import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.util.Triple;
import org.key_project.slicing.graph.AnnotatedEdge;
import org.key_project.slicing.graph.ClosedGoal;
import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.graph.TrackedFormula;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Implementation of the dependency analysis algorithm.
 *
 * @author Arne Keller
 */
public final class DependencyAnalyzer {
    private static final Logger LOGGER = LoggerFactory.getLogger(DependencyAnalyzer.class);
    private final boolean doDependencyAnalysis;
    private final boolean doDeduplicateRuleApps;

    private final Proof proof;
    private final DependencyGraph graph;
    private final Set<Node> usefulSteps = new HashSet<>();
    private final Set<GraphNode> usefulFormulas = new HashSet<>();
    private final Set<BranchLocation> uselessBranches = new HashSet<>();
    private final Map<Node, List<Node>> branchStacks = new HashMap<>();

    public DependencyAnalyzer(
            Proof proof,
            DependencyGraph graph,
            boolean doDependencyAnalysis,
            boolean doDeduplicateRuleApps
    ) {
        this.proof = proof;
        this.graph = graph;
        this.doDependencyAnalysis = doDependencyAnalysis;
        this.doDeduplicateRuleApps = doDeduplicateRuleApps;
    }

    public AnalysisResults analyze() {
        if (GeneralSettings.noPruningClosed) {
            throw new IllegalStateException("cannot analyze proof with no (recorded) closed goals, "
                    + "try disabling GeneralSettings.noPruningClosed");
        }
        if (proof == null || !proof.closed()) {
            return null;
        }

        if (doDependencyAnalysis) {
            analyzeDependencies();
        }
        if (!doDependencyAnalysis && doDeduplicateRuleApps) {
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
        }
        if (doDeduplicateRuleApps) {
            deduplicateRuleApps();
        }


        // add a note to each useless proof step to allow easy identification by the user
        // TODO: make this configurable / add a different indicator?
        var queue = new ArrayDeque<Node>();
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

        return new AnalysisResults(proof, steps, usefulSteps.size(), rules, usefulSteps, usefulFormulas, uselessBranches, branchStacks, doDependencyAnalysis, doDeduplicateRuleApps);
    }

    private void analyzeDependencies() {
        // BFS, starting from all closed goals
        var queue = new ArrayDeque<Node>();
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
            if (node.childrenCount() <= 1) {
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
    }

    private void deduplicateRuleApps() {
        // search for duplicate rule applications
        graph.nodes().forEach(node -> {
            // debugging filter:
            /*
            if (!graph.incomingEdgesOf(node).allMatch(node1 -> node1.serialNr() == 42)) {
                return;
            }
             */

            // groups rule apps on this node by their rule (+ their output formula + inAntec)
            var foundDupes = new HashMap<Triple<RuleApp, SequentFormula, Boolean>, List<AnnotatedEdge>>();
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
                    return; // only try to deduplicate the addition of new formulas
                }
                var formula = (TrackedFormula) produced;
                foundDupes.computeIfAbsent(new Triple<>(
                                        proofNode.getAppliedRuleApp(),
                                        formula.formula,
                                        formula.inAntec),
                                _a -> new ArrayList<>())
                        .add(t.third);
            });

            for (var entry : foundDupes.entrySet()) {
                var steps = entry.getValue();
                if (steps.size() <= 1) {
                    continue;
                }
                // try merging "adjacent" rule apps
                // (rule apps are sorted by serial nr ≈ location in the proof tree)
                LOGGER.info("input {} found duplicate; attempt to merge:", node.toString(true, false));
                var apps = new ArrayList<>(steps);
                var locs = steps.stream()
                        .map(e -> e.proofStep.branchLocation())
                        .collect(Collectors.toList());
                var idxA = 0;
                var idxB = 1;
                while (idxB < steps.size()) {
                    LOGGER.info("idxes {} {}", idxA, idxB);
                    if (idxA >= idxB) {
                        idxB++;
                        continue;
                    }
                    var edgeA = apps.get(idxA);
                    if (edgeA == null) {
                        idxA++;
                        continue;
                    }
                    var edgeB = apps.get(idxB);
                    if (edgeB == null) {
                        // TODO does this actually happen?
                        idxB++;
                        continue;
                    }
                    var stepA = edgeA.proofStep;
                    var stepB = edgeB.proofStep;
                    //LOGGER.info("considering {} {}", stepA.serialNr(), stepB.serialNr());
                    var locA = locs.get(idxA);
                    var locB = locs.get(idxB);
                    if (locA.equals(locB)) {
                        // skip duplicates in the same branch...
                        idxA += 2;
                        idxB += 2;
                        continue;
                    }
                    var mergeBase = BranchLocation.commonPrefix(locA, locB);
                    // search for conflicting rule apps
                    // are any of the inputs consumed by any other edge?
                    var hasConflict = Stream.concat(
                            graph.inputsOf(stepA), graph.inputsOf(stepB)
                    ).anyMatch(
                            graphNode -> graph
                                    .edgesConsuming(graphNode)
                                    .filter(edgeX -> edgeX.proofStep.branchLocation().hasPrefix(mergeBase))
                                    .anyMatch(edgeX ->
                                            edgeX.proofStep != stepA && edgeX.proofStep != stepB));
                    if (hasConflict) {
                        // can't merge => proceed with next pair
                        idxA++;
                        idxB++;
                    } else {
                        // merge step B into step A
                        LOGGER.info("merging {} and {}", stepA.serialNr(), stepB.serialNr());
                        locs.set(idxA, mergeBase);
                        apps.set(idxB, null);
                        idxB++;
                    }
                }
                for (int i = 0; i < apps.size(); i++) {
                    var keep = apps.get(i) != null;
                    var originalLoc = steps.get(i).proofStep.branchLocation();
                    LOGGER.info("step {} kept? {}", steps.get(i).proofStep.serialNr(), keep);
                    if (keep && locs.get(i) != originalLoc) {
                        var differingSuffix = originalLoc.stripPrefix(locs.get(i));
                        LOGGER.info("should be done before branching node {}", differingSuffix);
                        branchStacks.computeIfAbsent(
                                        differingSuffix.getNode(0),
                                        _node -> new ArrayList<>())
                                .add(steps.get(i).proofStep);
                    }
                    if (!keep) {
                        usefulSteps.remove(steps.get(i).proofStep);
                    }
                }
            }
        });
    }
}
