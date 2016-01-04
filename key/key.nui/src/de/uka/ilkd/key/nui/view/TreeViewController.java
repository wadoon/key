package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.embed.swing.SwingNode;
import javafx.fxml.FXML;
import javafx.scene.layout.StackPane;

@KeYView(title = "Tree", path = "TreeView.fxml", preferredPosition = ViewPosition.TOPLEFT)
public class TreeViewController extends ViewController {

    private final SwingNode swingNode = new SwingNode();

    @FXML
    private StackPane stackPane;

    @Override
    public void initialize(URL location, ResourceBundle resources) {
    }

    @Override
    public void initializeAfterLoadingFxml() {
        createSwingContent(swingNode);
        stackPane.getChildren().add(swingNode);
    }
}
