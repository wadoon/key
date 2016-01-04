package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.application.Platform;
import javafx.embed.swing.SwingNode;
import javafx.fxml.FXML;
import javafx.scene.layout.StackPane;

@KeYView(title = "Tree", path = "TreeView.fxml", preferredPosition = ViewPosition.TOPLEFT)
public class TreeViewController extends ViewController {

    private ProofTreeView proofTreeView;

    @FXML
    private final SwingNode swingNode = new SwingNode();

    @FXML
    private StackPane stackPane;

    @Override
    public void initialize(URL location, ResourceBundle resources) {
    }

    @Override
    public void initializeAfterLoadingFxml() {
        proofTreeView = new ProofTreeView(context.getProofManager().getMediator());
        createSwingContent(swingNode);
        stackPane.getChildren().add(swingNode);
    }

    private void createSwingContent(final SwingNode swingNode) {
        Platform.runLater(() -> {
            swingNode.setContent(proofTreeView);
        });
    }
}
