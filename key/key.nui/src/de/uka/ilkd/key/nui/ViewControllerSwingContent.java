package de.uka.ilkd.key.nui;

import java.net.URL;
import java.util.ResourceBundle;

import javafx.embed.swing.SwingNode;

/**
 * This is the super class for any view controller that is supposed to embed Swing content.
 * @author Nils Muzzulini
 *
 */
public class ViewControllerSwingContent extends ViewController {

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        // TODO Auto-generated method stub
        
    }
    
    /**
     * This method embeds Swing Content into a view. If implemented it needs to be called after the FXML is loaded.
     * @param swingNode
     */
    public void createSwingContent(final SwingNode swingNode) {
        
    }

}
