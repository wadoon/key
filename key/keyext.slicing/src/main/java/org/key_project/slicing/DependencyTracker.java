package org.key_project.slicing;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.init.AbstractPO;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.proofevent.NodeChangeAddFormula;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.merge.CloseAfterMergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedMultigraph;
import org.key_project.slicing.graph.AddedRule;
import org.key_project.slicing.graph.ClosedGoal;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.graph.PseudoInput;
import org.key_project.slicing.graph.PseudoOutput;
import org.key_project.slicing.graph.TrackedFormula;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class DependencyTracker implements RuleAppListener, ProofTreeListener {
    private Proof proof;
    private final List<TrackedFormula> formulas = new ArrayList<>();
    private final Graph<GraphNode, DefaultEdge> graph = new DirectedMultigraph<>(DefaultEdge.class);
    private final Map<DefaultEdge, Node> edgeData = new IdentityHashMap<>();
    /**
     * Dependencies between edges. Only used for taclets that add new rules to the proof.
     */
    private final Map<Node, Node> edgeDependencies = new IdentityHashMap<>();
    private AnalysisResults analysisResults = null;
    private final Set<Goal> ignoredGoals = new HashSet<>();

    private final Map<Node, Node> replayedNodes = new IdentityHashMap<>();

    private static Set<PosInOccurrence> inputsOfRuleApp(RuleApp ruleApp, Node node) {
        var inputs = new HashSet<PosInOccurrence>();
        if (ruleApp.posInOccurrence() != null) {
            inputs.add(ruleApp.posInOccurrence().topLevel());
        }
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
        if (ruleApp instanceof MergeRuleBuiltInRuleApp || ruleApp instanceof CloseAfterMergeRuleBuiltInRuleApp) {
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

        var input = new ArrayList<GraphNode>();
        var output = new ArrayList<GraphNode>();

        // check for rules added by taclets
        var rule = n.getAppliedRuleApp().rule();
        if (rule instanceof Taclet) {
            var taclet = (Taclet) rule;
            if (taclet.getAddedBy() != null) {
                edgeDependencies.put(n, taclet.getAddedBy());
                input.add(new AddedRule(taclet.name().toString()));
            }
        }
        ruleAppInfo.getReplacementNodes().forEachRemaining(newNode -> {
                for (var newRule : newNode.getNode().getLocalIntroducedRules()) {
                    if (newRule.rule() instanceof Taclet && ((Taclet) newRule.rule()).getAddedBy() == n) {
                            output.add(new AddedRule(newRule.rule().name().toString()));
                    }
                }
        });

        // regular inputs
        for (var in : inputsOfRuleApp(ruleApp, n)) {
            var loc = n.branchLocation();
            var size = loc.size();
            var added = false;
            for (int i = 0; i <= size; i++) {
                var formula = new TrackedFormula(in.sequentFormula(), loc, in.isInAntec(), proof.getServices());
                if (formulas.contains(formula)) {
                    input.add(formula);
                    added = true;
                    break;
                }
                if (loc.size() > 0) {
                    var list = loc.toList();
                    list.remove(list.size() - 1);
                    loc = ImmutableList.fromList(list);
                }
            }
            if (!added) {
                // TODO: should only happen for initial sequent?
                var formula = new TrackedFormula(in.sequentFormula(), loc, in.isInAntec(), proof.getServices());
                input.add(formula);
            }
        }

        var outputs = new ArrayList<Pair<PosInOccurrence, String>>();

        int sibling = ruleAppInfo.getReplacementNodesList().size() - 1;
        for (var b : ruleAppInfo.getReplacementNodesList()) {
            String id = ruleAppInfo.getReplacementNodesList().size() > 1 ? ("" + sibling) : "";
            b.getNodeChanges().forEachRemaining(c -> {
                if (c instanceof NodeChangeAddFormula) {
                    outputs.add(new Pair<>(c.getPos(), id));
                }
            });
            sibling--;
        }

        for (var out : outputs) {
            var loc = n.branchLocation();
            if (!out.second.equals("")) {
                loc = loc.append("/" + n.serialNr() + "_" + out.second);
            }
            var formula = new TrackedFormula(out.first.sequentFormula(), loc, out.first.isInAntec(), proof.getServices());
            formulas.add(formula);
            output.add(formula);
        }

        if (goalList.isEmpty() || (ruleApp instanceof TacletApp &&
                ((TacletApp) ruleApp).taclet().closeGoal())) {
            output.add(new ClosedGoal(n.serialNr() + 1)); // TODO: is it always the next nr?
        }

        n.register(new DependencyNodeData(input, output, ruleApp.rule().displayName() + "_" + n.serialNr()), DependencyNodeData.class);

        // add pseudo nodes so the rule application is always included in the graph
        if (input.isEmpty()) {
            input.add(new PseudoInput());
        }
        if (output.isEmpty()) {
            output.add(new PseudoOutput());
        }

        for (var in : input) {
            for (var out : output) {
                graph.addVertex(in);
                graph.addVertex(out);
                if (graph.containsEdge(in, out)) {
                    continue;
                }
                var edge = new DefaultEdge();
                graph.addEdge(in, out, edge);
                edgeData.put(edge, n);
            }
        }
    }

    @Override
    public void proofPruned(ProofTreeEvent e) {
        // clean up removed formulas / nodes /...
        analysisResults = null;
        for (var edge : graph.edgeSet().toArray(new DefaultEdge[0])) {
            var node = edgeData.get(edge);
            if (!e.getSource().find(node) || node.getAppliedRuleApp() == null) {
                var data = node.lookup(DependencyNodeData.class);
                for (var out : data.outputs) {
                    graph.removeVertex(out);
                }
            }
        }
    }

    public String exportDot(boolean abbreviateFormulas) {
        var buf = new StringBuilder();
        buf.append("digraph {\n");
        buf.append("edge [dir=\"back\"];\n");
        var queue = new ArrayList<Node>();
        queue.add(proof.root());
        while (!queue.isEmpty()) {
            var node = queue.remove(queue.size() - 1);
            node.childrenIterator().forEachRemaining(queue::add);
            var data = node.lookup(DependencyNodeData.class);
            if (data == null) {
                continue;
            }
            for (var in : data.inputs) {
                data.outputs.stream().map(it -> it.toString(abbreviateFormulas)).forEach(out -> {
                    buf
                            .append('"')
                            .append(in.toString(abbreviateFormulas))
                            .append("\" -> \"")
                            .append(out)
                            .append("\" [label=\"")
                            .append(data.label);
                    if (analysisResults != null && !analysisResults.usefulSteps.contains(node)) {
                        buf.append("\" color=\"red");
                    }
                    buf
                            .append("\"]\n");
                });
            }
        }
        if (analysisResults != null) {
            for (var formula : formulas) {
                if (!analysisResults.usefulFormulas.contains(formula)) {
                    buf.append('"').append(formula.toString(abbreviateFormulas)).append('"').append(" [color=\"red\"]\n");
                }
            }
        }
        buf.append("}");
        return buf.toString();
    }

    public AnalysisResults analyze() {
        if (GeneralSettings.noPruningClosed) {
            throw new IllegalStateException("cannot analyze proof with no (recorded) closed goals, try disabling GeneralSettings.noPruningClosed");
        }
        if (proof == null || !proof.closed()) {
            return null;
        }
        if (analysisResults != null) {
            return analysisResults;
        }
        var usefulSteps = new HashSet<Node>();
        var usefulFormulas = new HashSet<TrackedFormula>();
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
            for (var input : data.inputs) {
                if (input instanceof TrackedFormula) {
                    usefulFormulas.add((TrackedFormula) input);
                }
            }
            for (var in : data.inputs) {
                graph.incomingEdgesOf(in).stream().map(edgeData::get).forEach(queue::add);
            }
        }

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
        proof.breadthFirstSearch(proof.root(), (_proof, node) -> {
            if (node.getAppliedRuleApp() == null) {
                return;
            }
            var displayName = node.getAppliedRuleApp().rule().displayName();
            if (!rules.containsKey(displayName)) {
                rules.put(displayName, new Triple<>(0, 0, 0));
            }
            var triple = rules.get(displayName);
            var d2 = !usefulSteps.contains(node) ? 1 : 0;
            var d3 = d2 == 1 && node.lookup(DependencyNodeData.class).inputs.stream().anyMatch(usefulFormulas::contains) ? 1 : 0;
            rules.put(displayName, new Triple<>(triple.first + 1, triple.second + d2, triple.third + d3));
        });

        analysisResults = new AnalysisResults(steps, usefulSteps.size(), rules, usefulSteps, usefulFormulas);
        return analysisResults;
    }

    public Proof sliceProof() {
        if (analysisResults == null) {
            return null;
        }
        ignoredGoals.clear();
        replayedNodes.clear();
        Proof p = null;
        var it = proof.getServices().getSpecificationRepository().getProofOblInput(proof);
        if (it != null) {
            if (it instanceof AbstractPO) {
                var po = ((AbstractPO) it).getNewPO();
                try {
                    new ProblemInitializer(proof.getServices().getProfile()).setUpProofHelper(it, po);
                    p = po.getFirstProof();
                    p.getServices()
                            .getSpecificationRepository().registerProof(it, p);
                } catch (ProofInputException e) {
                    e.printStackTrace();
                }
            }
        }
        if (p == null) {
            // note: this constructor only works for "simple" proof inputs (≈ pure logic)
            p = new Proof("reduced", proof.root().sequent().succedent().get(0).formula(), proof.header(), proof.getInitConfig().copy());
        }
        replayProof(p, proof.root());
        return p;
    }

    private void replayProof(Proof p, Node inputNode) {
        var node = inputNode;
        while (true) {
            if (node.getAppliedRuleApp() == null) {
                return;
            }
            if (analysisResults.usefulSteps.contains(node) || node.childrenCount() > 1) { // TODO: cut elimination
                System.out.println("at node " + node.serialNr() + " " + node.getAppliedRuleApp().rule().displayName());

                var app = node.getAppliedRuleApp();
                if (app instanceof MergeRuleBuiltInRuleApp) {
                    // re-construct merge rule
                    var pio = app.posInOccurrence();

                    var newApp = MergeRule.INSTANCE.createApp(pio, p.getServices());

                    if (!newApp.complete()) {
                        newApp = newApp.forceInstantiate(p.openGoals().stream().filter(it -> !ignoredGoals.contains(it)).findFirst().get());
                    }
                    app = newApp;
                }
                if (app instanceof CloseAfterMergeRuleBuiltInRuleApp) {
                    var toIgnore = p.openGoals().stream().filter(it -> !ignoredGoals.contains(it)).findFirst().get();
                    ignoredGoals.add(toIgnore);
                    // this goal will be closed automatically when the merge is complete
                    // CloseAfterMerge applications are done by the MergeRule!
                } else {
                    var goal = p.openGoals().stream().filter(it -> !ignoredGoals.contains(it)).findFirst().get();
                    // fix sequent object identity
                    var origSequent = node.sequent();
                    var ourSequent = goal.sequent();
                    var origSemisequents = new Semisequent[]{origSequent.antecedent(), origSequent.succedent()};
                    var ourSemisequents = new Semisequent[]{ourSequent.antecedent(), ourSequent.succedent()};
                    var idx = 1;
                    for (int j = 0; j < origSemisequents.length; j++) {
                        var origAnte = origSemisequents[j];
                        var ourAnte = ourSemisequents[j];
                        for (int i = 0; i < ourAnte.size(); i++) {
                            var pio = PosInOccurrence.findInSequent(ourSequent, idx, PosInTerm.getTopLevel());
                            if (!origAnte.contains(pio.sequentFormula())) {
                                // replace with equal object
                                for (var origFormula : origAnte.asList()) {
                                    if (origFormula.realEquals(pio.sequentFormula())) {
                                        ourAnte = ourAnte.replace(i, origFormula).semisequent();
                                        if (!origFormula.toString().equals(pio.sequentFormula().toString())) {
                                            System.err.println("catastrophic failure");
                                        }
                                    }
                                }
                            }
                            idx++;
                        }
                        ourSemisequents[j] = ourAnte;
                    }
                    goal.node().setSequent(Sequent.createSequent(ourSemisequents[0], ourSemisequents[1]));
                    // Register name proposals
                    p.getServices().getNameRecorder().setProposals(node.getNameRecorder().getProposals());
                    replayedNodes.put(node, goal.node());
                    if (app.rule() instanceof Taclet && ((Taclet) app.rule()).getAddedBy() != null) {
                        // find the correct rule app
                        boolean done = false;
                        for (var partialApp : goal.ruleAppIndex().tacletIndex().getPartialInstantiatedApps()) {
                            if (partialApp.taclet().getAddedBy() == replayedNodes.get(edgeDependencies.get(node))) {
                                // re-apply the taclet
                                var fullApp = partialApp.matchFind(app.posInOccurrence(), p.getServices()).setPosInOccurrence(app.posInOccurrence(), p.getServices());
                                //assert fullApp != null && fullApp.complete();
                                goal.apply(fullApp);
                                done = true;
                                break;
                            }
                        }
                        if (!done) {
                            goal.apply(app);
                        }
                    } else {
                        goal.apply(app);
                    }
                }
            }
            if (node.childrenCount() > 1) {
                List<Node> nodes = new ArrayList<>();
                node.childrenIterator().forEachRemaining(nodes::add);
                for (int i = nodes.size() - 1; i >= 0; i--) {
                    replayProof(p, nodes.get(i));
                }
                break;
            } else if (node.childrenCount() == 1) {
                node = node.child(0);
            } else {
                break;
            }
        }
    }

    public Node getNodeThatProduced(Node currentNode, PosInOccurrence pio) {
        if (proof == null) {
            return null;
        }
        var loc = currentNode.branchLocation();
        while (true) {
            var incoming = graph.incomingEdgesOf(new TrackedFormula(pio.sequentFormula(), loc, pio.isInAntec(), proof.getServices()));
            if (!incoming.isEmpty()) {
                return edgeData.get(incoming.stream().findFirst().get());
            }
            if (loc.isEmpty()) {
                break;
            }
            var list = loc.toList();
            list.remove(list.size() - 1);
            loc = ImmutableList.fromList(list);
        }
        return null;
    }
}
