package org.key_project.slicing;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.proofevent.NodeChangeAddFormula;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Pair;

import java.util.ArrayList;
import java.util.List;

public class DependencyTracker implements RuleAppListener {
    private Proof proof;
    private final List<String> producedFormulas = new ArrayList<>();

    @Override
    public void ruleApplied(ProofEvent e) {
        var proof = e.getSource();
        this.proof = proof;
        var ruleAppInfo = e.getRuleAppInfo();
        var ruleApp = ruleAppInfo.getRuleApp();
        var goalList = e.getNewGoals();
        var n = ruleAppInfo.getOriginalNode();

        var inputs = new ArrayList<PosInOccurrence>();
        var outputs = new ArrayList<Pair<PosInOccurrence, String>>();
        inputs.add(ruleApp.posInOccurrence().topLevel());
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

        String seqArrow = "⟹";
        var inputStrings = new ArrayList<String>();
        for (var in : inputs) {
            String input = LogicPrinter.quickPrintTerm(in.sequentFormula().formula(), proof.getServices(), true, true).trim();
            var loc = n.branchLocation();
            var finalId = input;
            for (int i = 0; i <= loc.size(); i++) {
                finalId = input + loc.stream().limit(i).reduce("", String::concat);
                finalId = !in.isInAntec() ? (seqArrow + " " + finalId) : (finalId + " " + seqArrow);
                if (producedFormulas.contains(finalId)) {
                    break;
                }
            }
            inputStrings.add(finalId);
        }
        var outputStrings = new ArrayList<String>();
        if (goalList.isEmpty()) {
            outputStrings.add("closed goal " + n.serialNr());
        } else if (ruleApp instanceof TacletApp &&
                    ((TacletApp) ruleApp).taclet().closeGoal()) {
            // the first new goal is the one to be closed
            outputStrings.add("closed goal " + n.serialNr());
        }
        for (var out : outputs) {
            String o = LogicPrinter.quickPrintTerm(out.first.sequentFormula().formula(), proof.getServices(), true, true).trim();
            String id = o + n.branchLocation().stream().reduce("", String::concat);
            if (!out.second.equals("")) {
                id = id + "/" + n.serialNr() + "_" + out.second;
            }
            String finalId = !out.first.isInAntec() ? (seqArrow + " " + id) : (id + " " + seqArrow);
            /*
            if (!producedFormulas.isEmpty()) {
                String last = producedFormulas.get(producedFormulas.size() - 1);
                System.out.println("\"" + last + "\" -> \"" + finalId + "\" [color=\"white\"]");
            }
             */
            producedFormulas.add(finalId);
            /*
            if (id.indexOf('/') != -1) {
                System.out.println("subgraph \"cluster_" + id.split("/", 2)[1] + "\" {");
                System.out.println("\"" + finalId + "\"");
                System.out.println("}");
            }
             */
            outputStrings.add(finalId);
        }

        n.register(new DependencyNodeData(inputStrings, outputStrings, ruleApp.rule().displayName() + "_" + n.serialNr()), DependencyNodeData.class);
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
                for (var out : data.outputs) {
                    buf.append('"').append(in).append("\" -> \"").append(out).append("\" [label=\"").append(data.label).append("\"]");
                }
            }
        }
        buf.append("}");
        return buf.toString();
    }
}
