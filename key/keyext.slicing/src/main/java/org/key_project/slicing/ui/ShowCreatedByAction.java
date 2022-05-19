package org.key_project.slicing.ui;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.proof.Node;

import java.awt.event.ActionEvent;

public class ShowCreatedByAction extends MainWindowAction {

    private static final long serialVersionUID = -1666859714803539089L;
    private final transient Node node;

    public ShowCreatedByAction(MainWindow mw, Node node) {
        super(mw);
        setName("Show proof step that created this formula");
        this.node = node;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        getMediator().getSelectionModel().setSelectedNode(node);
    }
}
