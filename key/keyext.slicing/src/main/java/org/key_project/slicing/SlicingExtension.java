package org.key_project.slicing;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.ContextMenuAdapter;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeListener;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.event.ActionEvent;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

@KeYGuiExtension.Info(name = "Slicing",
        description = "Author: Arne Keller <arne.keller@student.kit.edu>",
        experimental = true,
        optional = true,
        priority = 9001)
public class SlicingExtension implements KeYGuiExtension,
        KeYGuiExtension.ContextMenu,
        KeYGuiExtension.Startup,
        KeYGuiExtension.MainMenu, KeYGuiExtension.StatusLine {
    private final Map<Proof, DependencyTracker> trackers = new IdentityHashMap<>();
    private Proof currentProof = null;

    private final ContextMenuAdapter adapter = new ContextMenuAdapter() {
        @Override
        public List<Action> getContextActions(KeYMediator mediator, ContextMenuKind kind, PosInSequent pos) {
            return super.getContextActions(mediator, kind, pos);
        }
    };

    private final ProofTreeListener proofTreeListener = new ProofTreeAdapter() {

        public void proofPruned(de.uka.ilkd.key.proof.ProofTreeEvent e) {

        }
    };

    @Nonnull
    @Override
    public List<Action> getContextActions(@Nonnull KeYMediator mediator,
                                          @Nonnull ContextMenuKind kind,
                                          @Nonnull Object underlyingObject) {
        return adapter.getContextActions(mediator, kind, underlyingObject);
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        System.out.println("init called");
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                // ignored
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                Proof newProof = mediator.getSelectedProof();
                if (!trackers.containsKey(newProof)) {
                    var tracker = new DependencyTracker();
                    newProof.addRuleAppListener(tracker);
                    trackers.put(newProof, tracker);
                }
                currentProof = newProof;
            }
        });

        //window.getProofTreeView().getRenderer().add(new ExplorationRenderer());
    }

    /*
    @Nonnull
    @Override
    public Collection<TabPanel> getPanels(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        if (leftPanel == null) leftPanel = new ExplorationStepsList(window);
        return Collections.singleton(leftPanel);
    }
     */

    @Override
    public List<JComponent> getStatusLineComponents() {
        var button = new JButton("Export DOT");
        button.addActionListener(e -> exportDot(e));
        return Collections.singletonList(button);
    }

    private void exportDot(ActionEvent e) {
        if (currentProof == null) {
            return;
        }
        KeYFileChooser fileChooser = KeYFileChooser.getFileChooser(
                "Choose filename to save dot file");
        fileChooser.setFileFilter(KeYFileChooser.DOT_FILTER);
        fileChooser.setSelectedFile(new File("export.dot"));
        int result = fileChooser.showSaveDialog((JComponent) e.getSource());
        if (result == JFileChooser.APPROVE_OPTION) {
            File file = fileChooser.getSelectedFile();
            try(BufferedWriter writer = new BufferedWriter(
                    new OutputStreamWriter(new FileOutputStream(file)));) {
                String text = trackers.get(currentProof).exportDot();
                writer.write(text);
            } catch (IOException any) {
                any.printStackTrace();
                assert false;
            }
        }
    }

    @Override
    public @Nonnull
    List<Action> getMainMenuActions(@Nonnull MainWindow mainWindow) {
        return Arrays.asList();
    }
}
