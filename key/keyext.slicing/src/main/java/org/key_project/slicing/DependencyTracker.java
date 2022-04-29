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

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

public class DependencyTracker implements RuleAppListener {
    private Proof proof;
    private final List<TrackedFormula> formulas = new ArrayList<>();

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

        var closedGoals = new ArrayList<String>();
        if (goalList.isEmpty() || (ruleApp instanceof TacletApp &&
                ((TacletApp) ruleApp).taclet().closeGoal())) {
            closedGoals.add("closed goal " + (n.serialNr() + 1)); // TODO: is it always the next nr?
        }

        var input = new ArrayList<TrackedFormula>();
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
                Stream.concat(data.outputs.stream().map(Object::toString), data.closedGoals.stream()).forEach(out -> buf
                        .append('"')
                        .append(in)
                        .append("\" -> \"")
                        .append(out)
                        .append("\" [label=\"")
                        .append(data.label)
                        .append("\"]\n"));
            }
        }
        buf.append("}");
        return buf.toString();
    }
}
