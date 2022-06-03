package org.key_project.slicing;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractPO;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.merge.CloseAfterMergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class ProofSlicer {
    private final Proof proof;
    private final AnalysisResults analysisResults;
    private final Map<Node, Node> edgeDependencies;
    private final Set<Goal> ignoredGoals = new HashSet<>();
    private final Map<Node, Node> replayedNodes = new IdentityHashMap<>();

    public ProofSlicer(
            Proof proof,
            AnalysisResults analysisResults,
            Map<Node, Node> edgeDependencies
    ) {
        if (proof == null || analysisResults == null || edgeDependencies == null) {
            throw new NullPointerException();
        }
        this.proof = proof;
        this.analysisResults = analysisResults;
        this.edgeDependencies = edgeDependencies;
    }

    public Proof sliceProof() {
        if (MainWindow.hasInstance()) {
            MainWindow.getInstance().setStatusLine(
                    "Slicing proof", analysisResults.usefulSteps.size());
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
            System.err.println("cloning proof using fallback method");
            // note: this constructor only works for "simple" proof inputs (≈ pure logic)
            p = new Proof(
                    "reduced",
                    proof.root().sequent().succedent().get(0).formula(),
                    proof.header(),
                    proof.getInitConfig().copy()
            );
        }
        // reset index counters, so we hopefully get the same indices
        p.getServices().resetCounters();
        OneStepSimplifier.refreshOSS(p);
        replayProof(p, proof.root());
        return p;
    }

    private void replayProof(Proof p, Node inputNode) {
        var node = inputNode;
        while (true) {
            if (node.getAppliedRuleApp() == null) {
                return; // closed goal
            }
            if (!analysisResults.usefulSteps.contains(node) && node.childrenCount() > 1) {
                System.err.println("about to skip cut @ node " + node.serialNr());
            }
            if (analysisResults.usefulSteps.contains(node)) { // TODO: cut elimination
                System.err.println("at node " + node.serialNr() + " " + node.getAppliedRuleApp().rule().displayName());
                /*
                try {
                    p.saveToFile(new java.io.File("/tmp/before" + node.serialNr() + ".proof"));
                } catch (Throwable t) {

                }
                 */

                var app = node.getAppliedRuleApp();

                // handle State Merging rules
                if (app instanceof MergeRuleBuiltInRuleApp) {
                    // re-construct merge rule
                    var pio = app.posInOccurrence();

                    var newApp = MergeRule.INSTANCE.createApp(pio, p.getServices());

                    if (!newApp.complete()) {
                        newApp = newApp.forceInstantiate(getCurrentGoal(p));
                    }
                    app = newApp;
                }
                if (app instanceof CloseAfterMergeRuleBuiltInRuleApp) {
                    var toIgnore = getCurrentGoal(p);
                    ignoredGoals.add(toIgnore);
                    // this goal will be closed automatically when the merge is complete
                    // CloseAfterMerge applications are done by the MergeRule!
                } else {
                    var goal = getCurrentGoal(p);
                    // fix sequent object identity
                    // then we can re-apply the steps done in the original proof
                    var origSequent = node.sequent();
                    var ourSequent = goal.sequent();
                    var origSemisequents = new Semisequent[] {
                            origSequent.antecedent(), origSequent.succedent()
                    };
                    var ourSemisequents = new Semisequent[] {
                            ourSequent.antecedent(), ourSequent.succedent()
                    };
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
                                            System.err.println("name / index mismatch");
                                            System.err.println(origFormula);
                                            System.err.println(pio.sequentFormula());
                                            // TODO: check whether this still happens
                                        }
                                    }
                                }
                            }
                            idx++;
                        }
                        ourSemisequents[j] = ourAnte;
                    }
                    goal.node().setSequent(Sequent.createSequent(ourSemisequents[0], ourSemisequents[1]));
                    // register name proposals
                    p.getServices().getNameRecorder()
                            .setProposals(node.getNameRecorder().getProposals());
                    replayedNodes.put(node, goal.node());

                    // restrict OSS applications
                    if (app instanceof OneStepSimplifierRuleApp) {
                        ((OneStepSimplifierRuleApp) app).restrictedIfInsts = true;
                    }
                    // handle rules added dynamically by other proof steps
                    if (app.rule() instanceof Taclet
                            && ((Taclet) app.rule()).getAddedBy() != null) {
                        // find the correct rule app
                        boolean done = false;
                        for (var partialApp : goal.ruleAppIndex().tacletIndex().getPartialInstantiatedApps()) {
                            if (partialApp.taclet().getAddedBy() == replayedNodes.get(edgeDependencies.get(node))) {
                                // re-apply the taclet
                                var fullApp = partialApp
                                        .matchFind(app.posInOccurrence(), p.getServices())
                                        .setPosInOccurrence(app.posInOccurrence(), p.getServices());
                                //assert fullApp != null && fullApp.complete();
                                goal.apply(fullApp);
                                done = true;
                                break;
                            }
                        }
                        if (!done) {
                            throw new IllegalStateException(
                                    "Proof Slicer failed to find dynamically added taclet!");
                        }
                    } else {
                        goal.apply(app);
                    }
                    if (MainWindow.hasInstance()) {
                        MainWindow.getInstance()
                                .getUserInterface().setProgress(replayedNodes.size());
                    }
                }
            }
            if (node.childrenCount() == 0) {
                break;
            }
            if (node.childrenCount() > 1 && analysisResults.usefulSteps.contains(node)) {
                List<Node> nodes = new ArrayList<>();
                node.childrenIterator().forEachRemaining(nodes::add);
                for (int i = nodes.size() - 1; i >= 0; i--) {
                    replayProof(p, nodes.get(i));
                }
                break;
            } else {
                // if the split was not useful, we only descend into the first sub-tree
                // TODO: perhaps descend into the shortest one (if they are not equal?!)
                node = node.child(0);
            }
        }
    }

    private Goal getCurrentGoal(Proof p) {
        var goal = p.openGoals().stream().filter(it -> !ignoredGoals.contains(it)).findFirst();
        if (goal.isEmpty()) {
            throw new IllegalStateException("Proof Slicer ran out of open goals!");
        }
        return goal.get();
    }
}
