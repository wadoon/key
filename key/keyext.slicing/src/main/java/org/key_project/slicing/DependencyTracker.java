package org.key_project.slicing;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.proofevent.NodeChangeAddFormula;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Pair;
import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedMultigraph;

import javax.swing.*;
import java.io.File;
import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

public class DependencyTracker implements RuleAppListener {
    private Proof proof;
    private final List<TrackedFormula> formulas = new ArrayList<>();
    private final Graph<GraphNode, DefaultEdge> graph = new DirectedMultigraph<>(DefaultEdge.class);
    private final Map<DefaultEdge, Node> edgeData = new IdentityHashMap<>();
    private boolean analysisDone = false;
    private final Set<Node> usefulSteps = new HashSet<>();
    private final Set<TrackedFormula> usefulFormulas = new HashSet<>();

    // TODO: track proof pruning
    // TODO: investigate One Step Simplifications: their inputs are not recorded properly!

    public DependencyTracker(Proof proof) {
        this.proof = proof;
    }

    @Override
    public void ruleApplied(ProofEvent e) {
        var proof = e.getSource();
        this.proof = proof;
        var ruleAppInfo = e.getRuleAppInfo();
        var ruleApp = ruleAppInfo.getRuleApp();
        var goalList = e.getNewGoals();
        var n = ruleAppInfo.getOriginalNode();
        //System.out.println("processing rule app " + n.getAppliedRuleApp().rule().displayName());

        var inputs = new ArrayList<PosInOccurrence>();
        var outputs = new ArrayList<Pair<PosInOccurrence, String>>();
        if (ruleApp.posInOccurrence() != null) {
            inputs.add(ruleApp.posInOccurrence().topLevel());
        } // some taclets don't have this kind of input, e.g. sign_case_distinction
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
                loc = loc.tail();
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
                var edge = new DefaultEdge();
                graph.addEdge(in, out, edge);
                edgeData.put(edge, n);
            }
        }
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

    public void analyze(JComponent parent) {
        if (proof == null || !proof.closed()) {
            return;
        }
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

        var window = SwingUtilities.getWindowAncestor(parent);
        var dialog = new JDialog(window, "Analysis results");
        var steps = proof.countNodes() - proof.closedGoals().size();
        var text = "Total steps: " + steps + "<br>"
                + "Useful steps: " + usefulSteps.size() + "<br>"
                + "Unnecessary steps: " + (steps - usefulSteps.size());
        JEditorPane statisticsPane = new JEditorPane("text/html", text);
        statisticsPane.setEditable(false);
        dialog.add(statisticsPane);
        dialog.pack();
        dialog.setLocationRelativeTo(window);
        dialog.setVisible(true);

        Proof p = new Proof("reduced", proof.root().sequent().succedent().get(0).formula(), proof.header(), proof.getInitConfig().copy());
        replayProof(p, proof.root());
        try {
            p.saveToFile(new File("/tmp/testing.proof"));
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private void replayProof(Proof p, Node node) {
        if (node.getAppliedRuleApp() == null) {
            return;
        }
        if (usefulSteps.contains(node)) {
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
