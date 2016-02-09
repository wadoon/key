package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.event.EventHandler;
import javafx.event.EventType;
import javafx.fxml.FXML;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

@KeYView(title = "Proofs", path = "ProofBrowserView.fxml", preferredPosition = ViewPosition.BOTTOMRIGHT)
public class ProofBrowserViewController extends ViewController {

    @FXML
    private TreeView<String> tableView;

    private TreeItem<String> rootItem = new TreeItem<String> ("Proofs");
    private int count = 0;
    
    private KeYSelectionListener proofChangeListener = new KeYSelectionListener() {
        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {
            addProofToBrowser(e.toString());
        }

        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
        }
    };
    
    @Override
    public void initialize(URL location, ResourceBundle resources) {
        rootItem.setExpanded(true);
        tableView.setRoot(rootItem);
        tableView.getSelectionModel().selectedItemProperty().addListener(new ChangeListener<TreeItem<String>>() {
            @Override
            public void changed(
                    ObservableValue<? extends TreeItem<String>> observable,
                    TreeItem<String> old_val, TreeItem<String> new_val) {
                TreeItem<String> selectedItem = new_val;
                System.out.println("Selected tree item : " + selectedItem.getValue());
            }
        });
    }
    
    @Override
    public void initializeAfterLoadingFxml() {
        getContext().getKeYMediator().addKeYSelectionListener(proofChangeListener);
    }
    
    public void addProofToBrowser(String s) {
        for (TreeItem<String> treeItem : rootItem.getChildren()) {
            if (treeItem.getValue().equals(s)) {
                return;
            }
        }

        TreeItem<String> newProof = new TreeItem<String>(s);
        rootItem.getChildren().add(newProof);
        tableView.getSelectionModel().select(newProof);
    }
    
    public void deleteProofFromBrowser() {
        int i = tableView.getSelectionModel().getSelectedIndex() - 1;
        if (i < 0) {
            return;
        }
        rootItem.getChildren().remove(i);
    }
    
    @FXML
    private void clickMe() {
        addProofToBrowser("test " + count);
        count++;
    }
    
    @FXML
    private void delete() {
        deleteProofFromBrowser();
    }

}
