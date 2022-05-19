package org.key_project.slicing;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.ContextMenuAdapter;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Proof;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.util.Arrays;
import java.util.Collection;
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
        KeYGuiExtension.MainMenu, KeYGuiExtension.LeftPanel {
    public final Map<Proof, DependencyTracker> trackers = new IdentityHashMap<>();
    public Proof currentProof = null;
    private SlicingLeftPanel leftPanel = null;

    private final ContextMenuAdapter adapter = new ContextMenuAdapter() {
        @Override
        public List<Action> getContextActions(KeYMediator mediator, ContextMenuKind kind, PosInSequent pos) {
            return super.getContextActions(mediator, kind, pos);
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
                    newProof.addProofTreeListener(tracker);
                    trackers.put(newProof, tracker);
                }
                currentProof = newProof;
                leftPanel.proofSelected();
            }
        });
        mediator.registerProofLoadListener(newProof -> {
            if (!trackers.containsKey(newProof)) {
                if (newProof != null) {
                    var tracker = new DependencyTracker();
                    newProof.addRuleAppListener(tracker);
                    trackers.put(newProof, tracker);
                }
            }
            currentProof = newProof;
        });

        //window.getProofTreeView().getRenderer().add(new ExplorationRenderer());
    }

    @Nonnull
    @Override
    public Collection<TabPanel> getPanels(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        if (leftPanel == null) leftPanel = new SlicingLeftPanel(mediator, this);
        return Collections.singleton(leftPanel);
    }

    @Override
    public @Nonnull
    List<Action> getMainMenuActions(@Nonnull MainWindow mainWindow) {
        return List.of();
    }
}
