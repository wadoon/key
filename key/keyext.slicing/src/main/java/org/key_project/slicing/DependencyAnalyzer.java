package org.key_project.slicing;

import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.merge.CloseAfterMergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.util.EqualsModProofIrrelevancyWrapper;
import de.uka.ilkd.key.util.Triple;
import org.key_project.slicing.graph.AnnotatedEdge;
import org.key_project.slicing.graph.ClosedGoal;
import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.graph.TrackedFormula;
import org.key_project.slicing.util.ExecutionTime;
import org.key_project.slicing.util.NoHashCode;
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
import java.util.concurrent.atomic.AtomicInteger;
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

        if (doDependencyAnalysis) {
            executionTime.start(DEPENDENCY_ANALYSIS);
            analyzeDependencies();
            executionTime.end(DEPENDENCY_ANALYSIS);
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
            executionTime.end(DUPLICATE_ANALYSIS_SETUP);
        }
        if (doDeduplicateRuleApps) {
            executionTime.start(DUPLICATE_ANALYSIS);
            deduplicateRuleApps();
            executionTime.end(DUPLICATE_ANALYSIS);
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
        executionTime.end(TOTAL_WORK);

        return new AnalysisResults(
                proof,
                steps,
                usefulSteps.size(),
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
                graph.incomingEdgesOf(in.first).forEach(queue::add);
            }
            if (considerOutputs) {
                data.outputs.stream().filter(ClosedGoal.class::isInstance).forEach(usefulFormulas::add);
            }
        }
        executionTime.end(DEPENDENCY_ANALYSIS2);

        // analyze cuts: they are only useful if all of their outputs were used
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
                // TODO: perhaps keep the "smallest" branch?
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
        executionTime.end(DEPENDENCY_ANALYSIS3);

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
        executionTime.end(DEPENDENCY_ANALYSIS4);
    }

    private void deduplicateRuleApps() {
        var alreadyRebasedSerialNrs = new HashSet<Integer>();
        var alreadyMergedSerialNrs = new HashSet<Integer>();
        // search for duplicate rule applications
        graph.nodes().forEach(node -> {
            // debugging filter:
            /*
            if (!graph.incomingEdgesOf(node).allMatch(node1 -> node1.serialNr() == 42)) {
                return;
            }
             */

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
                var steps = new ArrayList<>(entry.getValue());
                if (steps.size() <= 1) {
                    continue;
                }
                steps.sort(Comparator.comparing(it -> it.stepIndex));
                // try merging "adjacent" rule apps
                // (rule apps are sorted by step index = linear location in the proof tree)
                LOGGER.info("input {} found duplicate; attempt to merge:", node.toString(false, false));
                var apps = new ArrayList<>(steps);
                var locs = steps.stream()
                        .map(Node::branchLocation)
                        .collect(Collectors.toList());
                var idxA = 0;
                var idxB = 1;
                while (idxB < steps.size()) {
                    LOGGER.info("idxes {} {}", idxA, idxB);
                    if (idxA >= idxB) {
                        idxB++;
                        continue;
                    }
                    var stepA = apps.get(idxA);
                    if (stepA == null) {
                        idxA++;
                        continue;
                    }
                    var stepB = apps.get(idxB);
                    if (stepB == null) {
                        // TODO does this actually happen?
                        idxB++;
                        continue;
                    }
                    LOGGER.info("idxes updated {} {}", idxA, idxB);
                    // check whether this rule app consumes a formula
                    var consumesInput = graph.edgesOf(apps.get(idxA)).stream().anyMatch(it -> it.consumesInput);
                    if (alreadyMergedSerialNrs.contains(stepA.serialNr())
                            || (idxA == idxB - 1 && alreadyRebasedSerialNrs.contains(stepA.serialNr()))) {
                        idxA++;
                        continue;
                    }
                    // can't merge/rebase a step twice!
                    if (alreadyMergedSerialNrs.contains(stepB.serialNr())
                            || alreadyRebasedSerialNrs.contains(stepB.serialNr())) {
                        idxB++;
                        continue;
                    }
                    LOGGER.info("considering {} {}", stepA.serialNr(), stepB.serialNr());
                    var locA = locs.get(idxA);
                    var locB = locs.get(idxB);
                    if (locA.equals(locB)) {
                        // skip duplicates in the same branch...
                        idxB++;
                        continue;
                    }
                    var mergeBase = BranchLocation.commonPrefix(locA, locB);
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
                        LOGGER.info("hasConflict = {}", hasConflict);
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
                        for (var stepAB : new Node[] {stepA, stepB}) {
                            graph.outputsOf(stepAB).forEach(graphNode -> {
                                // check whether other rule apps also produce this node, and whether it is consumed before we need it
                                var createIdx = stepAB.stepIndex;
                                AtomicInteger prevCreateIdx = new AtomicInteger(-1);
                                AtomicInteger prevConsumeIdx = new AtomicInteger(-1);
                                AtomicInteger plannedConsumeIdx = new AtomicInteger(-1);
                                while (graphNode.getBranchLocation().size() >= mergeBase.size()) {
                                    graph.outgoingGraphEdgesOf(graphNode).forEach(triple -> {
                                        var idx = triple.first.stepIndex;
                                        if (triple.third.consumesInput) {
                                            if (idx > createIdx && (plannedConsumeIdx.get() == -1 || idx < plannedConsumeIdx.get())) {
                                                plannedConsumeIdx.set(idx);
                                            }
                                            if (idx < createIdx && (prevConsumeIdx.get() == -1 || idx > prevConsumeIdx.get())) {
                                                prevConsumeIdx.set(idx);
                                            }
                                        }
                                    });
                                    graph.incomingGraphEdgesOf(graphNode).forEach(triple -> {
                                        var idx = triple.first.stepIndex;
                                        if (idx < createIdx && (prevCreateIdx.get() == -1 || idx > prevCreateIdx.get())) {
                                            prevCreateIdx.set(idx);
                                        }
                                    });
                                    if (graphNode.getBranchLocation().isEmpty()) {
                                        break;
                                    }
                                    graphNode = graphNode.popLastBranchID();
                                }
                                hasConflictOut.set(hasConflictOut.get() || (plannedConsumeIdx.get() != -1 && prevConsumeIdx.get() != -1 && prevCreateIdx.get() < prevConsumeIdx.get()));
                            });
                        }
                    }
                    if (hasConflict || hasConflictOut.get() || !mergeValid) {
                        // can't merge => proceed with next pair
                        idxA++;
                        idxB++;
                    } else {
                        // merge step B into step A
                        LOGGER.info("merging {} and {}", stepA.serialNr(), stepB.serialNr());
                        locs.set(idxA, mergeBase);
                        alreadyRebasedSerialNrs.add(stepA.serialNr());
                        apps.set(idxB, null);
                        alreadyMergedSerialNrs.add(stepB.serialNr());
                        idxB++;
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
