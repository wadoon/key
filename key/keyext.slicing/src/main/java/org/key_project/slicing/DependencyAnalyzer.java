package org.key_project.slicing;

import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.merge.CloseAfterMergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.util.EqualsModProofIrrelevancyWrapper;
import de.uka.ilkd.key.util.Pair;
import org.key_project.slicing.graph.ClosedGoal;
import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.graph.TrackedFormula;
import org.key_project.slicing.util.ExecutionTime;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Implementation of both dependency analysis algorithms.
 *
 * @author Arne Keller
 */
public final class DependencyAnalyzer {
    private static final String TOTAL_WORK = "0 (total time)";
    private static final String DEPENDENCY_ANALYSIS = "1 Dependency Analysis";
    private static final String DEPENDENCY_ANALYSIS2 = "1a Dependency Analysis: search starting @ closed goals";
    private static final String DEPENDENCY_ANALYSIS3 = "1b Dependency Analysis: analyze branching nodes";
    private static final String DEPENDENCY_ANALYSIS4 = "1c Dependency Analysis: final mark of useless steps";
    private static final String DUPLICATE_ANALYSIS = "2 Duplicate Analysis";
    private static final String DUPLICATE_ANALYSIS_SETUP = "~ Duplicate Analysis setup";
    private static final boolean DUPLICATES_SAFE_MODE = true;

    private static final Logger LOGGER = LoggerFactory.getLogger(DependencyAnalyzer.class);
    private final boolean doDependencyAnalysis;
    private final boolean doDeduplicateRuleApps;

    private final Proof proof;
    private final DependencyGraph graph;
    private final Set<Node> usefulSteps = new HashSet<>();
    private final Set<GraphNode> usefulFormulas = new HashSet<>();
    private final Set<BranchLocation> uselessBranches = new HashSet<>();
    private final Map<Node, List<Node>> branchStacks = new HashMap<>();
    private final ExecutionTime executionTime = new ExecutionTime();

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

        executionTime.start(TOTAL_WORK);
        proof.setStepIndices();

        if (doDependencyAnalysis) {
            executionTime.start(DEPENDENCY_ANALYSIS);
            analyzeDependencies();
            executionTime.stop(DEPENDENCY_ANALYSIS);
        }

        if (!doDependencyAnalysis && doDeduplicateRuleApps) {
            executionTime.start(DUPLICATE_ANALYSIS_SETUP);
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
            executionTime.stop(DUPLICATE_ANALYSIS_SETUP);
        }

        if (doDeduplicateRuleApps) {
            executionTime.start(DUPLICATE_ANALYSIS);
            deduplicateRuleApps();
            executionTime.stop(DUPLICATE_ANALYSIS);
        }


        // add a note to each useless proof step to allow easy identification by the user
        // TODO: make this configurable / add a different indicator?
        var queue = new ArrayDeque<Node>();
        queue.add(proof.root());
        while (!queue.isEmpty()) {
            var node = queue.pop();
            if (!usefulSteps.contains(node)) {
                node.getNodeInfo().setNotes("useless");
            } else if (Objects.equals(node.getNodeInfo().getNotes(), "useless")) {
                node.getNodeInfo().setNotes(null);
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
        executionTime.stop(TOTAL_WORK);

        return new AnalysisResults(
                proof,
                steps,
                rules,
                usefulSteps,
                usefulFormulas,
                uselessBranches,
                branchStacks,
                doDependencyAnalysis,
                doDeduplicateRuleApps,
                executionTime
        );
    }

    private void analyzeDependencies() {
        // BFS, starting from all closed goals
        var queue = new ArrayDeque<Node>();
        for (var e : proof.closedGoals()) {
            queue.add(e.node());
        }

        executionTime.start(DEPENDENCY_ANALYSIS2);
        while (!queue.isEmpty()) {
            var node = queue.pop();
            // handle State Merging
            if (node.getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp
                    || node.getAppliedRuleApp() instanceof CloseAfterMergeRuleBuiltInRuleApp) {
                throw new IllegalStateException("tried to analyze proof featuring state merging!");
            }

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
                var thisProofStep = node;
                graph
                        .incomingEdgesOf(in.first)
                        // we don't care about steps done to derive the same formula again!
                        .filter(step -> step.stepIndex < thisProofStep.stepIndex)
                        .forEach(queue::add);
            }
            if (considerOutputs) {
                data.outputs.stream().filter(ClosedGoal.class::isInstance).forEach(usefulFormulas::add);
            }
        }
        executionTime.stop(DEPENDENCY_ANALYSIS2);

        // analyze branching proof steps: they are only useful if all of their outputs were used
        executionTime.start(DEPENDENCY_ANALYSIS3);
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
            // mark sub-proof as useless, if necessary
            var branchesToSkip = data.outputs.stream()
                    .filter(usefulFormulas::contains)
                    .map(GraphNode::getBranchLocation)
                    .collect(Collectors.toSet());
            var keptSomeBranch = false;
            for (var i = 0; i < node.childrenCount(); i++) {
                var branch = node.child(i);
                // need to keep exactly one branch
                // keep any, we expect them to be roughly equivalent?
                if (!keptSomeBranch && !branchesToSkip.contains(branch.branchLocation())) {
                    keptSomeBranch = true;
                    continue;
                }
                uselessBranches.add(branch.branchLocation());
            }
            if (!keptSomeBranch) {
                throw new IllegalStateException("dependency analyzer failed to analyze branching proof step!");
            }
        });
        executionTime.stop(DEPENDENCY_ANALYSIS3);

        // unmark all 'useful' steps in useless branches
        executionTime.start(DEPENDENCY_ANALYSIS4);
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
        executionTime.stop(DEPENDENCY_ANALYSIS4);
    }

    private boolean mergedAnything = false;

    private void deduplicateRuleApps() {
        var alreadyRebasedSerialNrs = new HashSet<Integer>();
        var alreadyMergedSerialNrs = new HashSet<Integer>();
        // search for duplicate rule applications
        graph.nodes().forEach(node -> {
            if (mergedAnything) {
                return;
            }
            // groups proof steps that act upon this graph node by their rule app
            // (for obvious reasons, we don't care about origin labels here -> wrapper)
            var foundDupes = new HashMap<EqualsModProofIrrelevancyWrapper<RuleApp>, Set<Node>>();
            graph.outgoingGraphEdgesOf(node).forEach(t -> {
                var proofNode = t.first;

                // handle State Merging
                if (proofNode.getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp
                        || proofNode.getAppliedRuleApp() instanceof CloseAfterMergeRuleBuiltInRuleApp) {
                    throw new IllegalStateException("tried to analyze proof featuring state merging!");
                }

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
                foundDupes.computeIfAbsent(new EqualsModProofIrrelevancyWrapper<>(proofNode.getAppliedRuleApp()),
                                _a -> new LinkedHashSet<>())
                        .add(t.third.proofStep);
            });

            for (var entry : foundDupes.entrySet()) {
                if (mergedAnything) {
                    continue;
                }
                var steps = new ArrayList<>(entry.getValue());
                if (steps.size() <= 1) {
                    continue;
                }
                steps.sort(Comparator.comparing(it -> it.stepIndex));
                // try merging "adjacent" rule apps
                // (rule apps are sorted by step index = linear location in the proof tree)
                LOGGER.trace("input {} found duplicate; attempt to merge:", node.toString(false, false));
                var apps = new ArrayList<>(steps);
                var locs = steps.stream()
                        .map(Node::branchLocation)
                        .collect(Collectors.toList());
                //var idxA = 0;
                //var idxB = 1;
                //while (idxB < steps.size()) {
                for (int idxA = 0; idxA < steps.size() - 1; idxA++) {
                    if (mergedAnything) {
                        continue;
                    }
                    var stepA = apps.get(idxA);
                    if (stepA == null) {
                        continue;
                    }
                    for (int idxB = idxA + 1; idxB < steps.size(); idxB++) {
                        if (mergedAnything) {
                            continue;
                        }
                        LOGGER.trace("idxes {} {}", idxA, idxB);
                        var stepB = apps.get(idxB);
                        if (stepB == null) {
                            // TODO does this actually happen?
                            continue;
                        }
                        LOGGER.trace("idxes used {} {}", idxA, idxB);
                        // check whether this rule app consumes a formula
                        var consumesInput = graph.edgesOf(apps.get(idxA)).stream().anyMatch(it -> it.consumesInput);
                        if (alreadyMergedSerialNrs.contains(stepA.serialNr())
                                || (idxA == idxB - 1 && alreadyRebasedSerialNrs.contains(stepA.serialNr()))) {
                            continue;
                        }
                        // can't merge/rebase a step twice!
                        if (alreadyMergedSerialNrs.contains(stepB.serialNr())
                                || alreadyRebasedSerialNrs.contains(stepB.serialNr())) {
                            continue;
                        }
                        LOGGER.trace("considering {} {}", stepA.serialNr(), stepB.serialNr());
                        var locA = locs.get(idxA);
                        var locB = locs.get(idxB);
                        if (locA.equals(locB)) {
                            // skip duplicates in the same branch...
                            continue;
                        }
                        var mergeBase = BranchLocation.commonPrefix(locA, locB);
                        var differingSuffix = locA.size() == mergeBase.size() ? locB : locA;
                        var newStepIdx = differingSuffix.stripPrefix(mergeBase).getNode(0).stepIndex - 1;
                        // verify that *all* inputs are present at the merge base
                        var mergeValid = Stream.concat(
                                graph.inputsOf(stepA), graph.inputsOf(stepB)
                        ).allMatch(graphNode -> mergeBase.hasPrefix(graphNode.getBranchLocation()));
                        // verify that they actually use the same inputs...
                        var inputsA = graph.inputsOf(stepA).collect(Collectors.toSet());
                        var inputsB = graph.inputsOf(stepB).collect(Collectors.toSet());
                        mergeValid = mergeValid && inputsA.containsAll(inputsB) && inputsB.containsAll(inputsA);
                        // search for conflicting rule apps
                        // (only relevant if the rule apps consume the input)
                        boolean hasConflict = false;
                        if (consumesInput && mergeValid) {
                            // are any of the inputs used by any other edge?
                            hasConflict = Stream.concat(
                                    graph.inputsConsumedBy(stepA), graph.inputsConsumedBy(stepB)
                            ).anyMatch(graphNode -> graph
                                    .edgesUsing(graphNode)
                                    // TODO: does this filter ever return false?
                                    .filter(edgeX -> edgeX.proofStep.branchLocation().hasPrefix(mergeBase))
                                    .anyMatch(edgeX ->
                                            edgeX.proofStep != stepA && edgeX.proofStep != stepB));
                            LOGGER.trace("hasConflict = {}", hasConflict);
                        }
                        // search for conflicting consumers of the output formulas
                        AtomicBoolean hasConflictOut = new AtomicBoolean(false);
                        if (mergeValid && !hasConflict) {
                            var usedInBranchesA = graph.outputsOf(stepA)
                                    .flatMap(n -> graph
                                            .edgesConsuming(n)
                                            .map(e -> e.proofStep.branchLocation()))
                                    .reduce(BranchLocation::commonPrefix);
                            var usedInBranchesB = graph.outputsOf(stepB)
                                    .flatMap(n -> graph
                                            .edgesConsuming(n)
                                            .map(e -> e.proofStep.branchLocation()))
                                    .reduce(BranchLocation::commonPrefix);
                            if (usedInBranchesA.isPresent() && usedInBranchesB.isPresent()) {
                                var branchA = usedInBranchesA.get();
                                var branchB = usedInBranchesB.get();
                                if (branchA.equals(branchB)) {
                                    throw new IllegalStateException("duplicate analyzer found impossible situation!");
                                }
                                hasConflictOut.set(branchA.equals(branchB));
                            }
                        }
                        // search for conflicts concerning multiple derivations of the same formula in a branch
                        if (mergeValid && !hasConflict && !hasConflictOut.get()) {
                            for (var stepAB : new Node[]{stepA, stepB}) {
                                graph.outputsOf(stepAB).forEach(graphNode -> {
                                    // get all equivalent graph nodes in this branch
                                    var allNodes = graph.nodeAndPreviousDerivations(graphNode);
                                    // get all steps that produce these / consume these
                                    var producers = allNodes.stream()
                                            .flatMap(graph::edgesProducing);
                                    var consumers = allNodes.stream()
                                            .flatMap(graph::edgesConsuming)
                                            .filter(x -> stepAB.branchLocation().hasPrefix(x.proofStep.branchLocation()));
                                    var lastConsumer = allNodes.stream()
                                            .flatMap(graph::edgesConsuming)
                                            .filter(edge -> !stepAB.branchLocation().hasPrefix(edge.proofStep.branchLocation())
                                                    && edge.proofStep.stepIndex > stepAB.stepIndex
                                                    && edge.proofStep.branchLocation().hasPrefix(stepAB.branchLocation()))
                                            .findFirst();
                                    if (lastConsumer.isPresent()) {
                                        consumers = Stream.concat(consumers, Stream.of(lastConsumer.get()));
                                    }
                                    // list of (step index, produces / consumes)
                                    var byStepIndex = Comparator.<Pair<Integer, Boolean>>comparingInt(x -> x.first);
                                    var list = Stream.concat(
                                                    producers.map(x -> new Pair<>(x.proofStep.stepIndex, true)),
                                                    consumers.map(x -> new Pair<>(x.proofStep.stepIndex, false))
                                            ).distinct()
                                            .sorted(byStepIndex)
                                            .collect(Collectors.toList());
                                    // verify that the list satisfies the correctness criteria
                                    Predicate<List<Pair<Integer, Boolean>>> isCorrect = l -> {
                                        var formulaAvailable = false;
                                        for (var pair : l) {
                                            if (pair.second) {
                                                formulaAvailable = true;
                                            } else if (!formulaAvailable) {
                                                return false;
                                            } else {
                                                formulaAvailable = false;
                                            }
                                        }
                                        return true;
                                    };
                                    if (!isCorrect.test(list)) {
                                        throw new IllegalStateException("analyzer failed to gather correct proof step list");
                                    }
                                    // reorder one proof step to simulate the merged proof
                                    list.remove(new Pair<>(stepAB.stepIndex, true));
                                    list.add(new Pair<>(newStepIdx, true));
                                    list.sort(byStepIndex);
                                    if (!isCorrect.test(list)) {
                                        hasConflictOut.set(true);
                                    }
                                });
                            }
                        }
                        if (!hasConflict && !hasConflictOut.get() && mergeValid) {
                            // merge step B into step A
                            LOGGER.info("merging {} and {}", stepA.serialNr(), stepB.serialNr());
                            locs.set(idxA, mergeBase);
                            alreadyRebasedSerialNrs.add(stepA.serialNr());
                            apps.set(idxB, null);
                            alreadyMergedSerialNrs.add(stepB.serialNr());
                            mergedAnything = DUPLICATES_SAFE_MODE;
                        }
                    }
                }
                for (int i = 0; i < apps.size(); i++) {
                    var keep = apps.get(i) != null;
                    var originalLoc = steps.get(i).branchLocation();
                    LOGGER.trace("step {} kept? {}", steps.get(i).serialNr(), keep);
                    if (keep && !locs.get(i).equals(originalLoc)) {
                        var differingSuffix = originalLoc.stripPrefix(locs.get(i));
                        LOGGER.trace("should be done before branching node {}", differingSuffix);
                        if (differingSuffix.isEmpty()) {
                            LOGGER.error("oh no");
                        }
                        branchStacks.computeIfAbsent(
                                        differingSuffix.getNode(0),
                                        _node -> new ArrayList<>())
                                .add(steps.get(i));
                    }
                    if (!keep) {
                        usefulSteps.remove(steps.get(i));
                    }
                }
            }
        });
    }
}
