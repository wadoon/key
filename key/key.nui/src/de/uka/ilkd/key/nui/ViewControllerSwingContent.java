package de.uka.ilkd.key.nui;

import de.uka.ilkd.key.java.statement.Return;
import javafx.embed.swing.SwingNode;
import javafx.fxml.FXML;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;

/**
 * This is an interface for any {@link ViewController} that is supposed to embed
 * Swing content. When creating the View Controller, it needs to extend this
 * class. The corresponding FXML file needs to be created as is JavaFX standard.
 * Its root {@link Pane} should be a {@link BorderPane}.
 * <p>
 * <b>Note:</b> {@link #createSwingContent()} is the only method that needs to
 * be implemented. Currently it needs to set the {@link SwingNode} using
 * {@link #getSwingNode()}.
 * <p>
 * {@link #createSwingContent()} can be modified to {@link Return} a
 * {@link JComponent} and use {@link #swingNode} as parameter.
 * <p>
 * If done so, the call to {@link #createSwingContent()} inside the body of
 * {@link #initializeAfterLoadingFxml()} must be replaced by {@link #swingNode}.
 * {@link javafx.embed.swing.SwingNode#setContent(javax.swing.JComponent)
 * setContent()} where the parameter of
 * {@link javafx.embed.swing.SwingNode#setContent(javax.swing.JComponent)
 * setContent()} must be a call to {@link #createSwingContent()}.
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
    public void initializeAfterLoadingFxml() {
        createSwingContent();
        stackPane.getChildren().add(swingNode);
    }

    /**
     * Embeds Swing content into a StackPane inside the view.
     * <p>
     * To implement use {@link #getSwingNode()}.
     * {@link javafx.embed.swing.SwingNode#setContent(javax.swing.JComponent)
     * setContent(JComponent)} where the {@link JComponent} is the Swing
     * Component to be added.
     * <p>
     * In the corresponding FXML file a {@link StackPane} with fx:id "stackPane"
     * needs to be added to the CENTER of the {@link BorderPane}.
     */
    public abstract void createSwingContent();

}
