package org.key_project.slicing;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
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
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.Pair;
import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedMultigraph;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

public class DependencyTracker implements RuleAppListener, ProofTreeListener {
    private Proof proof;
    private final List<TrackedFormula> formulas = new ArrayList<>();
    private final Graph<GraphNode, DefaultEdge> graph = new DirectedMultigraph<>(DefaultEdge.class);
    private final Map<DefaultEdge, Node> edgeData = new IdentityHashMap<>();
    private boolean analysisDone = false;
    public AnalysisResults analysisResults = null;
    private final Set<Node> usefulSteps = new HashSet<>();
    private final Set<TrackedFormula> usefulFormulas = new HashSet<>();

    public DependencyTracker() {
        GeneralSettings.noPruningClosed = false;
    }

    private static Set<PosInOccurrence> inputsOfRuleApp(RuleApp ruleApp) {
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
        if (ruleApp instanceof OneStepSimplifierRuleApp) {
            var oss = (OneStepSimplifierRuleApp) ruleApp;
            oss.ifInsts().forEach(inputs::add);
        }
        // TODO: other built-ins
        return inputs;
    }

    @Override
    public void ruleApplied(ProofEvent e) {
        this.proof = e.getSource();
        var ruleAppInfo = e.getRuleAppInfo();
        var ruleApp = ruleAppInfo.getRuleApp();
        var goalList = e.getNewGoals();
        var n = ruleAppInfo.getOriginalNode();

        var inputs = inputsOfRuleApp(ruleApp);
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

        var closedGoals = new ArrayList<String>();
        if (goalList.isEmpty() || (ruleApp instanceof TacletApp &&
                ((TacletApp) ruleApp).taclet().closeGoal())) {
            closedGoals.add("closed goal " + (n.serialNr() + 1)); // TODO: is it always the next nr?
        }

        var input = new ArrayList<GraphNode>();
        var output = new ArrayList<TrackedFormula>();
        for (var in : inputs) {
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

        for (var out : outputs) {
            var loc = n.branchLocation();
            if (!out.second.equals("")) {
                loc = loc.append("/" + n.serialNr() + "_" + out.second);
            }
            var formula = new TrackedFormula(out.first.sequentFormula(), loc, out.first.isInAntec(), proof.getServices());
            formulas.add(formula);
            output.add(formula);
        }

        n.register(new DependencyNodeData(input, output, closedGoals, ruleApp.rule().displayName() + "_" + n.serialNr()), DependencyNodeData.class);

        if (input.size() == 0) {
            input.add(new PseudoInput());
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
        // TODO: clean up removed formulas / nodes /...
        analysisDone = false;
    }

    public String exportDot() {
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
                Stream.concat(data.outputs.stream().map(Object::toString), data.closedGoals.stream()).forEach(out -> {
                    buf
                            .append('"')
                            .append(in)
                            .append("\" -> \"")
                            .append(out)
                            .append("\" [label=\"")
                            .append(data.label);
                    if (analysisDone && !usefulSteps.contains(node)) {
                        buf.append("\" color=\"red");
                    }
                    buf
                            .append("\"]\n");
                });
            }
        }
        if (analysisDone) {
            for (var formula : formulas) {
                if (!usefulFormulas.contains(formula)) {
                    buf.append('"').append(formula).append('"').append(" [color=\"red\"]\n");
                }
            }
        }
        buf.append("}");
        return buf.toString();
    }

    public AnalysisResults analyze() {
        if (proof == null || !proof.closed()) {
            return null;
        }
        if (analysisDone) {
            return analysisResults;
        }
        usefulSteps.clear();
        usefulFormulas.clear();
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
        analysisDone = true;

        queue.add(proof.root());
        while (!queue.isEmpty()) {
            var node = queue.pop();
            if (!usefulSteps.contains(node)) {
                node.getNodeInfo().setNotes("useless");
            }
            node.childrenIterator().forEachRemaining(queue::add);
        }

        var steps = proof.countNodes() - proof.closedGoals().size();
        analysisResults = new AnalysisResults(steps, usefulSteps.size());
        return analysisResults;
    }

    public Proof sliceProof() {
        if (!analysisDone) {
            return null;
        }
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

    private void replayProof(Proof p, Node node) {
        if (node.getAppliedRuleApp() == null) {
            return;
        }
        if (usefulSteps.contains(node) || node.childrenCount() > 1) { // TODO: cut elimination
            //System.out.println("at node " + node.serialNr() + " " + node.getAppliedRuleApp().rule().displayName());
            //System.out.println("applying..");
            var app = node.getAppliedRuleApp();
            p.openGoals().head().apply(app);
        }
        if (node.childrenCount() > 1) {
            List<Node> nodes = new ArrayList<>();
            node.childrenIterator().forEachRemaining(nodes::add);
            for (int i = nodes.size() - 1; i >= 0; i--) {
                replayProof(p, nodes.get(i));
            }
        } else if (node.childrenCount() == 1) {
            replayProof(p, node.child(0));
        }
    }
}
