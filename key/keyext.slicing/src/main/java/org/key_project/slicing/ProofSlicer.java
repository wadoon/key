package org.key_project.slicing;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.stream.Collectors;

public final class ProofSlicer {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofSlicer.class);

    private final Proof proof;
    private final AnalysisResults analysisResults;

    public ProofSlicer(
            Proof proof,
            AnalysisResults analysisResults
    ) {
        if (proof == null || analysisResults == null) {
            throw new NullPointerException();
        }
        this.proof = proof;
        this.analysisResults = analysisResults;
    }

    public Path sliceProof() {
        boolean loadInUI = MainWindow.hasInstance();
        if (loadInUI) {
            MainWindow.getInstance().setStatusLine(
                    "Slicing proof", analysisResults.usefulSteps.size());
        }
        var stepIndex = 0;
        var nodeIterator = proof.root().subtreeIterator();
        var toName = new HashMap<Integer, String>();
        while (nodeIterator.hasNext()) {
            var node = nodeIterator.next();
            node.stepIndex = stepIndex;
            toName.put(node.stepIndex, node.getAppliedRuleApp() != null ? node.getAppliedRuleApp().rule().name().toString() : "none");
            stepIndex++;
        }
        GeneralSettings.slicing = true;
        GeneralSettings.usefulSteps = analysisResults.usefulSteps.stream().map(node -> node.stepIndex).collect(Collectors.toSet());
        GeneralSettings.serialNrToPos = analysisResults
                .usefulSteps.stream()
                .map(node ->
                        new Pair<>(node.stepIndex, node.getAppliedRuleApp().posInOccurrence()))
                .filter(it -> it.second != null)
                .collect(Collectors.toMap(it -> it.first, it -> it.second));
        GeneralSettings.serialNrToName = toName;
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
        try {
            var tempFile = Files.createTempFile("", ".proof");
            proof.saveToFile(tempFile.toFile());
            return tempFile;
        } catch (IOException e) {
            LOGGER.error("failed to save temporary proof file", e);
        }
        throw new IllegalStateException("proof slicer failed to save proof");
    }
}
