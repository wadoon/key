package org.key_project.slicing;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.proofevent.NodeChangeAddFormula;
import de.uka.ilkd.key.proof.proofevent.NodeChangeRemoveFormula;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.merge.CloseAfterMergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.util.Pair;
import org.key_project.slicing.graph.AddedRule;
import org.key_project.slicing.graph.ClosedGoal;
import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.DotExporter;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.graph.PseudoInput;
import org.key_project.slicing.graph.PseudoOutput;
import org.key_project.slicing.graph.TrackedFormula;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;

public class DependencyTracker implements RuleAppListener, ProofTreeListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(DependencyTracker.class);

    /**
     * The proof this tracker monitors.
     */
    private Proof proof;
    private final DependencyGraph graph = new DependencyGraph();
    /**
     * Dependencies between edges. Only used for taclets that add new rules to the proof.
     */
    private final Map<Node, Node> edgeDependencies = new IdentityHashMap<>();
    private AnalysisResults analysisResults = null;

    /**
     * @param ruleApp a rule application
     * @param node node corresponding to the rule application
     * @return all formulas used as inputs by the rule application (\find, \assume, etc.)
     */
    private static Set<PosInOccurrence> inputsOfRuleApp(RuleApp ruleApp, Node node) {
        var inputs = new HashSet<PosInOccurrence>();
        if (ruleApp.posInOccurrence() != null) {
            inputs.add(ruleApp.posInOccurrence().topLevel());
        }
        inputs.addAll(ifInstsOfRuleApp(ruleApp, node));
        return inputs;
    }

    public static Set<PosInOccurrence> ifInstsOfRuleApp(RuleApp ruleApp, Node node) {
        var inputs = new HashSet<PosInOccurrence>();
        // taclets with \find or similar
        if (ruleApp instanceof PosTacletApp) {
            var posTacletApp = (PosTacletApp) ruleApp;
            if (posTacletApp.ifFormulaInstantiations() != null) {
                for (var x : posTacletApp.ifFormulaInstantiations()) {
                    if (x instanceof IfFormulaInstSeq) {
                        var antec = ((IfFormulaInstSeq) x).inAntec();
                        inputs.add(new PosInOccurrence(x.getConstrainedFormula(), PosInTerm.getTopLevel(), antec));
                    }
                }
            }
        }
        // built-ins need special treatment
        // OSS: record if instantiations
        if (ruleApp instanceof OneStepSimplifierRuleApp) {
            var oss = (OneStepSimplifierRuleApp) ruleApp;
            oss.ifInsts().forEach(inputs::add);
        }
        // State Merging: add all formulas as inputs
        // TODO: this is not enough, as the State Merge processes every formula in the sequent
        // (-> if more formulas are present after slicing, a different result will be produced!)
        // SMT application: add all formulas as inputs
        // TODO: this may be too much (see unsat core)
        if (ruleApp instanceof MergeRuleBuiltInRuleApp
                || ruleApp instanceof CloseAfterMergeRuleBuiltInRuleApp
                || ruleApp instanceof RuleAppSMT) {
            node.sequent().antecedent().iterator().forEachRemaining(it ->
                    inputs.add(new PosInOccurrence(it, PosInTerm.getTopLevel(), true))
            );
            node.sequent().succedent().iterator().forEachRemaining(it ->
                    inputs.add(new PosInOccurrence(it, PosInTerm.getTopLevel(), false))
            );
        }
        // TODO: other built-ins?
        return inputs;
    }

    @Override
    public void ruleApplied(ProofEvent e) {
        this.proof = e.getSource();
        var ruleAppInfo = e.getRuleAppInfo();
        var ruleApp = ruleAppInfo.getRuleApp();
        var goalList = e.getNewGoals();
        var n = ruleAppInfo.getOriginalNode();

        var input = new ArrayList<Pair<GraphNode, Boolean>>();
        var output = new ArrayList<GraphNode>();

        // check whether the rule of this proof step was added by another node
        var rule = n.getAppliedRuleApp().rule();
        if (rule instanceof Taclet) {
            var taclet = (Taclet) rule;
            if (taclet.getAddedBy() != null) {
                edgeDependencies.put(n, taclet.getAddedBy());
                input.add(new Pair<>(new AddedRule(taclet.name().toString()), false));
            }
        }

        // record any rules added by this rule application
        for (var newNode : ruleAppInfo.getReplacementNodes()) {
            for (var newRule : newNode.getNode().getLocalIntroducedRules()) {
                if (newRule.rule() instanceof Taclet
                        && ((Taclet) newRule.rule()).getAddedBy() == n) {
                    output.add(new AddedRule(newRule.rule().name().toString()));
                }
            }
        }

        // record removed (replaced) input formulas
        // TODO: this may be different for each branch (?)
        var removed = new HashSet<PosInOccurrence>();
        for (var newNode : ruleAppInfo.getReplacementNodes()) {
            newNode.getNodeChanges().forEachRemaining(nodeChange -> {
                if (nodeChange instanceof NodeChangeRemoveFormula) {
                    removed.add(nodeChange.getPos());
                }
            });
        }
        // record sequent formula inputs
        for (var in : inputsOfRuleApp(ruleApp, n)) {
            // need to find the used sequent formula in the graph
            // (requires knowing the branch it was produced in)
            var loc = n.branchLocation();
            var size = loc.size();
            var added = false;
            for (int i = 0; i <= size; i++) {
                var formula = new TrackedFormula(in.sequentFormula(), loc, in.isInAntec(), proof.getServices());
                if (graph.containsNode(formula)) {
                    input.add(new Pair<>(formula, removed.contains(in)));
                    added = true;
                    break;
                }
                if (loc.size() > 0) {
                    loc = loc.removeLast();
                }
            }
            if (!added) {
                // should only happen if the formula is the initial proof obligation
                if (!proof.root().sequent().contains(in.sequentFormula())) {
                    throw new IllegalStateException("found formula that was not produced by any rule!");
                }
                var formula = new TrackedFormula(in.sequentFormula(), loc, in.isInAntec(), proof.getServices());
                input.add(new Pair<>(formula, removed.contains(in)));
            }
        }

        var outputs = new ArrayList<Pair<PosInOccurrence, Integer>>();

        int sibling = ruleAppInfo.getReplacementNodes().size() - 1;
        for (var b : ruleAppInfo.getReplacementNodes()) {
            var id = ruleAppInfo.getReplacementNodes().size() > 1 ? sibling : -1;
            b.getNodeChanges().forEachRemaining(c -> {
                if (c instanceof NodeChangeAddFormula) {
                    outputs.add(new Pair<>(c.getPos(), id));
                }
            });
            sibling--;
        }

        for (var out : outputs) {
            var loc = n.branchLocation();
            if (out.second != -1) {
                loc = loc.append(new Pair<>(n, out.second));
            }
            var formula = new TrackedFormula(
                    out.first.sequentFormula(),
                    loc,
                    out.first.isInAntec(),
                    proof.getServices()
            );
            output.add(formula);
        }

        // add closed goals as output
        if (goalList.isEmpty() || (ruleApp instanceof TacletApp &&
                ((TacletApp) ruleApp).taclet().closeGoal())) {
            var closedGoal = proof.closedGoals()
                    .stream()
                    .filter(goal -> goal.node().parent() == n)
                    .findFirst();
            if (closedGoal.isPresent()) {
                output.add(new ClosedGoal(closedGoal.get().node().serialNr(), n.branchLocation()));
            } else {
                LOGGER.debug(
                        "Warning: did not locate the goal closed by step {}", n.serialNr());
                output.add(new ClosedGoal(n.serialNr() + 1, n.branchLocation()));
            }
        }

        n.register(new DependencyNodeData(
                input,
                output,
                ruleApp.rule().displayName() + "_" + n.serialNr()
        ), DependencyNodeData.class);

        // add pseudo nodes so the rule application is always included in the graph
        if (input.isEmpty()) {
            input.add(new Pair<>(new PseudoInput(), true));
        }
        if (output.isEmpty()) {
            output.add(new PseudoOutput());
        }

        // add new edges to graph
        graph.addRuleApplication(n, input, output);
    }

    @Override
    public void proofPruned(ProofTreeEvent e) {
        // clean up removed formulas / nodes /...
        analysisResults = null;
        graph.prune(e);
        // TODO: clean up formulas too?
    }

    public String exportDot(boolean abbreviateFormulas) {
        return DotExporter.exportDot(proof, graph, analysisResults, abbreviateFormulas);
    }

    public String exportDotAround(boolean abbreviateFormulas, boolean omitBranch, GraphNode node) {
        return DotExporter.exportDotAround(
                proof, graph, analysisResults, abbreviateFormulas, omitBranch, node);
    }

    public AnalysisResults analyze(boolean doDependencyAnalysis, boolean doDeduplicateRuleApps) {
        if (analysisResults != null
                && analysisResults.didDependencyAnalysis == doDependencyAnalysis
                && analysisResults.didDeduplicateRuleApps == doDeduplicateRuleApps) {
            return analysisResults;
        }
        analysisResults = new DependencyAnalyzer(
                proof, graph, doDependencyAnalysis, doDeduplicateRuleApps).analyze();
        return analysisResults;
    }

    public Path sliceProof() {
        return new ProofSlicer(proof, analysisResults).sliceProof();
    }

    public GraphNode getGraphNode(Node currentNode, PosInOccurrence pio) {
        if (proof == null) {
            return null;
        }
        var loc = currentNode.branchLocation();
        while (true) {
            var formula = new TrackedFormula(pio.sequentFormula(), loc, pio.isInAntec(), proof.getServices());
            if (graph.containsNode(formula)) {
                return formula;
            }
            if (loc.isEmpty()) {
                break;
            }
            loc = loc.removeLast();
        }
        return null;
    }

    public Node getNodeThatProduced(Node currentNode, PosInOccurrence pio) {
        if (proof == null) {
            return null;
        }
        var graphNode = getGraphNode(currentNode, pio);
        var incoming = graph.incomingEdgesOf(graphNode);
        var node = incoming.findFirst();
        return node.orElse(null);
    }

    public AnalysisResults getAnalysisResults() {
        return analysisResults;
    }

    /**
     * @return the dependency graph populated by this tracker
     */
    public DependencyGraph getDependencyGraph() {
        return graph;
    }
}
