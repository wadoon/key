package org.key_project.slicing;

import de.uka.ilkd.key.core.KeYMediator;
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
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.merge.CloseAfterMergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public final class ProofSlicer {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofSlicer.class);

    private final Proof proof;
    private final AnalysisResults analysisResults;
    private final Map<Node, Node> edgeDependencies;
    private final Set<Goal> ignoredGoals = new HashSet<>();
    private final Map<Node, Node> replayedNodes = new IdentityHashMap<>();
    private final boolean saveIntermediateSteps = false;
    private final boolean logAtInfo = false;

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

    public Proof sliceProof(KeYMediator mediator) {
        if (MainWindow.hasInstance()) {
            MainWindow.getInstance().setStatusLine(
                    "Slicing proof", analysisResults.usefulSteps.size());
        }
        var stepIndex = 0;
        var nodeIterator = proof.root().subtreeIterator();
        while (nodeIterator.hasNext()) {
            var node = nodeIterator.next();
            node.stepIndex = stepIndex;
            stepIndex++;
        }
        GeneralSettings.slicing = true;
        GeneralSettings.usefulSteps = analysisResults.usefulSteps.stream().map(node -> node.stepIndex).collect(Collectors.toSet());
        GeneralSettings.serialNrToPos = analysisResults
                .usefulSteps.stream()
                .map(node ->
                        new Pair<>(node.stepIndex, node.getAppliedRuleApp().posInOccurrence()))
                .collect(Collectors.toMap(it -> it.first, it -> it.second));
        GeneralSettings.serialNrToIfInsts = analysisResults
                .usefulSteps.stream()
                .map(node ->
                        new Pair<>(node.stepIndex, DependencyTracker.ifInstsOfRuleApp(node.getAppliedRuleApp(), node)))
                .collect(Collectors.toMap(it -> it.first, it -> it.second));
        GeneralSettings.stepIndexToDynamicRule = analysisResults
                .usefulSteps.stream()
                .filter(node -> node.getAppliedRuleApp() != null && node.getAppliedRuleApp().rule() instanceof Taclet && ((Taclet) node.getAppliedRuleApp().rule()).getAddedBy() != null)
                .map(node ->
                        new Pair<>(node.stepIndex, ((Taclet) node.getAppliedRuleApp().rule()).getAddedBy().stepIndex))
                .collect(Collectors.toMap(it -> it.first, it -> it.second));
        SwingUtilities.invokeLater(() ->
                mediator.getUI().loadProblem(new File("/tmp/x/x.proof"))
        );
        return null;
        /*
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
                    LOGGER.error("failed to duplicate proof obligation", e);
                }
            }
        }
        if (p == null) {
            LOGGER.debug("cloning proof using fallback method");
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
        if (GeneralSettings.disableOSSRestriction) {
            LOGGER.warn("OSS restriction is disabled, slicing may not work properly!");
        }
        try {
            p.saveToFile(new java.io.File("/tmp/AA_initial.proof"));
        } catch (Throwable t) {
            throw new IllegalStateException(t);
        }
        replayProof(p, proof.root());
        return p;
         */
    }

    private void replayProof(Proof p, Node inputNode) {
        var node = inputNode;
        while (true) {
            if (node.getAppliedRuleApp() == null) {
                return; // closed goal
            }
            if (!analysisResults.usefulSteps.contains(node) && node.childrenCount() > 1) {
                if (logAtInfo) {
                    LOGGER.info("about to skip cut @ node {}", node.serialNr());
                } else {
                    LOGGER.debug("about to skip cut @ node {}", node.serialNr());
                }
            }
            if (analysisResults.usefulSteps.contains(node)) {
                if (logAtInfo) {
                    LOGGER.info("at node {} {}", node.serialNr(), node.getAppliedRuleApp().rule().displayName());
                } else {
                    LOGGER.trace("at node {} {}", node.serialNr(), node.getAppliedRuleApp().rule().displayName());
                }
                if (saveIntermediateSteps) {
                    try {
                        p.saveToFile(new java.io.File("/tmp/before" + node.serialNr() + ".proof"));
                    } catch (Throwable t) {
                        throw new IllegalStateException(t);
                    }
                }

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
                                        if (logAtInfo) {
                                            LOGGER.info("replacing formula identity");
                                        } else {
                                            LOGGER.trace("replacing formula identity");
                                        }
                                        ourAnte = ourAnte.replace(i, origFormula).semisequent();
                                        // TODO: remove this rather expensive check if it never occurs
                                        /*
                                        if (!origFormula.toString().equals(pio.sequentFormula().toString())) {
                                            LOGGER.error("step {}: name / index mismatch {} {}", node.serialNr(), origFormula, pio.sequentFormula());
                                            throw new IllegalStateException("Proof Slicer failed to identify correct sequent formula!");
                                        }
                                         */
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
            if (node.childrenCount() > 1) {
                List<Node> nodes = new ArrayList<>();
                node.childrenIterator().forEachRemaining(nodes::add);
                boolean descendIntoAll = analysisResults.usefulSteps.contains(node);
                for (int i = nodes.size() - 1; i >= 0; i--) {
                    var childNode = nodes.get(i);
                    // if this branch of the split was not useful, we do not descend into it
                    if (analysisResults.branchIsUseful(childNode.branchLocation())) {
                        replayProof(p, childNode);
                        if (!descendIntoAll) {
                            // TODO: perhaps descend into the shortest one (if they are not equal?!)
                            break;
                        }
                    }
                }
                break;
            } else {
                node = node.child(0);
                //LOGGER.info("going to node {}", node.serialNr());
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
