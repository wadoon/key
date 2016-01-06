package de.uka.ilkd.key.nui.view.embeddedswingcontent;

import java.net.URL;
import java.util.ResourceBundle;

import javax.swing.JScrollPane;

import de.uka.ilkd.key.gui.GoalList;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewControllerSwingContent;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.embed.swing.SwingNode;
import javafx.fxml.FXML;
import javafx.scene.layout.StackPane;

@KeYView(title = "Open Goals", path = "OpenGoalsView.fxml", preferredPosition = ViewPosition.TOPRIGHT)
public class OpenGoalsViewController extends ViewControllerSwingContent {

    private final SwingNode swingNode = new SwingNode();
    private JScrollPane openGoalsView;

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

    @Override
    public void createSwingContent(SwingNode swingNode) {
        // set openGoalsView (From old UI)
        openGoalsView = new JScrollPane();
        //GuiUtilities.paintEmptyViewComponent(openGoalsView, "Open Goals");
        GoalList goalList = new GoalList(context.getProofManager().getMediator());
        openGoalsView.setViewportView(goalList);
        
        swingNode.setContent(openGoalsView);
    }
}
