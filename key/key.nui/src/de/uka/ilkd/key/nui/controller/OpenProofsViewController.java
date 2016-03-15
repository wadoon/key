package de.uka.ilkd.key.nui.controller;

import java.util.Observable;
import java.util.Observer;

import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.ListView;
import javafx.scene.control.MenuItem;
import javafx.scene.control.TextArea;

/**
 * Controller for the view showing an overview of all loaded proofs.
 * 
 * @author Florian Breitfelder
 */
@ControllerAnnotation(createMenu = true)
public class OpenProofsViewController extends NUIController
        implements Observer {

    @FXML
    TextArea textAreaOpenProofs;

    @FXML
    ListView<String> listView;

    private ContextMenu contextMenu;

    @Override
    protected void init() {
        dataModel.addObserver(this);
        // Define action to be performed if user clicks on a proof entry
        listView.setOnMouseClicked((event) -> {
            String selectedItem = listView.getSelectionModel()
                    .getSelectedItem();
            if (selectedItem != null) {
                dataModel.loadProofFormMemory(selectedItem);
            }
        });

        MenuItem deleteProof = new MenuItem(bundle.getString("closeProof"));
        contextMenu = new ContextMenu(deleteProof);
        // Define action to be performed if user clicks on 'Close Proof' in the
        // context menu
        deleteProof.setOnAction((event) -> dataModel
                .removeProof(listView.getSelectionModel().getSelectedItem()));
    }

    @Override
    public void update(Observable o, Object arg) {
        ObservableList<String> loadedProofs = dataModel.getListOfProofs();
        if (loadedProofs.size() >= 1) {
            listView.setContextMenu(contextMenu);
        }
        else {
            listView.setContextMenu(null);
        }
        listView.setItems(loadedProofs);
        listView.getSelectionModel().select(arg.toString());
    }

}
