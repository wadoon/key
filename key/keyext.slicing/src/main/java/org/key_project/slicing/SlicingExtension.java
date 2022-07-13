package org.key_project.slicing;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.ContextMenuAdapter;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.slicing.ui.ShowCreatedByAction;
import org.key_project.slicing.ui.ShowGraphAction;
import org.key_project.slicing.ui.ShowNodeInfoAction;
import org.key_project.slicing.ui.SlicingLeftPanel;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

@KeYGuiExtension.Info(name = "Slicing",
        description = "Author: Arne Keller <arne.keller@student.kit.edu>",
        experimental = false,
        optional = true,
        priority = 9001)
public class SlicingExtension implements KeYGuiExtension,
        KeYGuiExtension.ContextMenu,
        KeYGuiExtension.Startup,
        KeYGuiExtension.LeftPanel,
        KeYSelectionListener {

    /**
     * Collection of dependency trackers.
     *
     * TODO: delete tracker when the proof is closed?
     */
    public final Map<Proof, DependencyTracker> trackers = new IdentityHashMap<>();
    /**
     * The left panel inserted into the GUI.
     */
    private SlicingLeftPanel leftPanel = null;

    /**
     * The context menu adapter used by the extension.
     */
    private final ContextMenuAdapter adapter = new ContextMenuAdapter() {
        @Override
        public List<Action> getContextActions(
                KeYMediator mediator, ContextMenuKind kind, PosInSequent pos) {

            var tracker = trackers.get(mediator.getSelectedProof());
            if (tracker == null
                    || pos == null
                    || pos.getPosInOccurrence() == null
                    || pos.getPosInOccurrence().topLevel() == null
                    || mediator.getSelectedNode() == null) {
                return List.of();
            }
            var currentNode = mediator.getSelectedNode();
            var topLevel = pos.getPosInOccurrence().topLevel();
            var node = tracker.getNodeThatProduced(currentNode, topLevel);
            if (node == null) {
                return List.of();
            }
            var list = new ArrayList<Action>();
            list.add(new ShowCreatedByAction(MainWindow.getInstance(), node));
            var graphNode = tracker.getGraphNode(currentNode, topLevel);
            if (graphNode != null) {
                list.add(new ShowGraphAction(MainWindow.getInstance(), tracker, graphNode));
                list.add(new ShowNodeInfoAction(MainWindow.getInstance(), tracker, graphNode));
            }
            return list;
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
    public void selectedProofChanged(KeYSelectionEvent e) {
        createTrackerForProof(e.getSource().getSelectedProof());
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        mediator.addKeYSelectionListener(this);
        mediator.registerProofLoadListener(this::createTrackerForProof);
    }

    private void createTrackerForProof(Proof newProof) {
        trackers.computeIfAbsent(newProof, proof -> {
            if (proof == null) {
                return null;
            }
            var tracker = new DependencyTracker();
            proof.addRuleAppListener(tracker);
            proof.addProofTreeListener(tracker);
            return tracker;
        });
    }

    @Nonnull
    @Override
    public Collection<TabPanel> getPanels(
            @Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        if (leftPanel == null) {
            leftPanel = new SlicingLeftPanel(mediator, this);
            mediator.addKeYSelectionListener(leftPanel);
        }
        return Collections.singleton(leftPanel);
    }
}
