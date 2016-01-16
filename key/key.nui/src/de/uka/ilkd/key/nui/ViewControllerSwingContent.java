package de.uka.ilkd.key.nui;

import java.net.URL;
import java.util.ResourceBundle;

import javafx.embed.swing.SwingNode;
import javafx.fxml.FXML;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.StackPane;

/**
 * This is an interface for any View Controller that is supposed to embed Swing
 * content. When creating the View Controller needs to extend this class. The
 * corresponding FXML file needs to be created as is JavaFX standard. Its root
 * pane should be a {@link BorderPane}.
 * 
 * @author Nils Muzzulini
 * @version 1.0
 *
 */
public abstract class ViewControllerSwingContent extends ViewController {

    @FXML
    private StackPane stackPane;

    private final SwingNode swingNode = new SwingNode();

    public SwingNode getSwingNode() {
        return swingNode;
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
    }

    @Override
    public void initializeAfterLoadingFxml() {
        createSwingContent();
        stackPane.getChildren().add(swingNode);
    }

    /**
     * Embeds Swing content into a StackPane inside the view.
     * 
     * To implement use {@link #getSwingNode()}.
     * {@link javafx.embed.swing.SwingNode#setContent(javax.swing.JComponent)
     * setContent(JComponent)} where the {@link JComponent} is the Swing
     * Component to be added.
     * 
     * In the corresponding FXML file a {@link StackPane} with fx:id "stackPane"
     * needs to be added to the CENTER of the BorderPane.
     */
    public abstract void createSwingContent();

}
