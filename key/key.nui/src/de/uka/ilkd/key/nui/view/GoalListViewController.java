package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.embed.swing.SwingNode;
import javafx.fxml.FXML;
import javafx.scene.layout.StackPane;

//@KeYView(title = "Goal List", path = "GoalListView.fxml", preferredPosition = ViewPosition.TOPRIGHT)
public class GoalListViewController extends ViewController {

    private final SwingNode swingNodeG = new SwingNode();

    @FXML
    private StackPane stackPaneG;

    @Override
    public void initialize(URL location, ResourceBundle resources) {
    }

    @Override
    public void initializeAfterLoadingFxml() {
        createSwingContent(swingNodeG);
        stackPaneG.getChildren().add(swingNodeG);
    }

    @Override
    public void createSwingContent(SwingNode swingNode) {
        swingNode.setContent(context.getProofManager().getGoalList());
    }
}
