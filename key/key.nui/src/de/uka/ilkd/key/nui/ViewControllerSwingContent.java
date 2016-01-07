package de.uka.ilkd.key.nui;

import java.net.URL;
import java.util.ResourceBundle;

import javafx.embed.swing.SwingNode;
import javafx.fxml.FXML;
import javafx.scene.layout.StackPane;

/**
 * This is the super class for any view controller that is supposed to embed
 * Swing content.
 * 
 * @author Nils Muzzulini
 *
 */
public class ViewControllerSwingContent extends ViewController {

    @FXML
    private StackPane stackPane;

    private final SwingNode swingNode = new SwingNode();

    public SwingNode getSwingNode() {
        return swingNode;
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        // TODO Auto-generated method stub

    }

    @Override
    public void initializeAfterLoadingFxml() {
        createSwingContent();
        stackPane.getChildren().add(swingNode);
    }

    /**
     * Embeds Swing content into a StackPane inside the view. To implement use
     * {@link #getSwingNode()}.
     * {@link javafx.embed.swing.SwingNode#setContent(javax.swing.JComponent)
     * setContent(JComponent)} where the JComponent is the Swing Component to be
     * added.
     * 
     * In the corresponding FXML file a StackPane with fx:id "stackPane" needs
     * to be added.
     */
    public void createSwingContent() {

    }

}
