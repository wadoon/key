package org.key_project.slicing.ui;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.proof.Node;
import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.graph.GraphNode;

import javax.swing.*;
import java.awt.event.ActionEvent;

/**
 * Context menu action to display the dependency graph "around" a formula.
 *
 * @author Arne Keller
 */
public class ShowGraphAction extends MainWindowAction {

    private static final long serialVersionUID = -9022480738622934631L;

    private final transient DependencyTracker tracker;

    /**
     * The graph node to use.
     */
    private final transient GraphNode node;

    public ShowGraphAction(MainWindow mw, DependencyTracker tracker, GraphNode node) {
        super(mw);
        setName("Show dependency graph around this formula");
        this.tracker = tracker;
        this.node = node;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        String text = tracker.exportDotAround(false, true, node);
        new PreviewDialog(SwingUtilities.getWindowAncestor((JComponent) e.getSource()), text);
    }
}
