package de.uka.ilkd.key.kexext.backgroundSMT;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentListener;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
import java.util.*;
import java.util.List;
import java.util.stream.Collectors;

@KeYGuiExtension.Info(experimental = false, name = "BackgroundSMT")
public class BackgroundSMTExtension implements KeYGuiExtension, KeYGuiExtension.StatusLine, ProofEnvironmentListener {

    private ApplyBackgroundSolverAction applyAction = new ApplyBackgroundSolverAction();

    private Map<Proof, BackgroundSolverRunner> runners = new HashMap<>();

    @Override
    public List<JComponent> getStatusLineComponents() {
        JButton smtAlert = new JButton(applyAction);
        smtAlert.setText("hui");
        // TODO add as listener to ProofEnvironment?
        return List.of(smtAlert);
    }

    @Override
    public void proofRegistered(ProofEnvironmentEvent event) {
        for (Proof proof: Arrays.stream(event.getProofList().getProofs()).filter(p -> !runners.keySet().contains(p))
                .collect(Collectors.toList())) {
            BackgroundSolverRunner runner = new BackgroundSolverRunner(applyAction);
            proof.addRuleAppListener(runner);
            runners.put(proof, runner);
            proof.addRuleAppListener(runner);
        }
        applyAction.setRunner(runners.get(MainWindow.getInstance().getMediator().getSelectedProof()));
    }

    @Override
    public void proofUnregistered(ProofEnvironmentEvent event) {
        for (Proof proof: event.getProofList().getProofs()) {
            proof.removeRuleAppListener(runners.get(proof));
        }
    }

}