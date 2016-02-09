package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.HashMap;
import java.util.ResourceBundle;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.proof.Proof;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.fxml.FXML;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

@KeYView(title = "Proofs", path = "ProofBrowserView.fxml", preferredPosition = ViewPosition.BOTTOMRIGHT)
public class ProofBrowserViewController extends ViewController {

    @FXML
    private TreeView<String> tableView;

    private final static TreeItem<String> PROOF_BROWSER_ROOT_NODE = new TreeItem<String> ("Proofs");
    private Proof proof;
    
    private HashMap<String, Proof> listOfProofs = new HashMap<String, Proof>();
    
    private KeYSelectionListener proofChangeListener = new KeYSelectionListener() {
        @Override
        public void selectedProofChanged(KeYSelectionEvent event) {
            proof = event.getSource().getSelectedProof();
            addProofToBrowser();
        }

        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
        }
    };
    
    @Override
    public void initialize(URL location, ResourceBundle resources) {
        PROOF_BROWSER_ROOT_NODE.setExpanded(true);
        tableView.setRoot(PROOF_BROWSER_ROOT_NODE);
        tableView.getSelectionModel().selectedItemProperty().addListener(new ChangeListener<TreeItem<String>>() {
            @Override
            public void changed(
                    ObservableValue<? extends TreeItem<String>> observable,
                    TreeItem<String> old_val, TreeItem<String> new_val) {
                TreeItem<String> selectedItem = new_val;
                System.out.println("Selected tree item : " + selectedItem.getValue());
                
                /*if (hm.containsKey(selectedItem.getValue())) {
                    System.out.println(hm.get(selectedItem.getValue()));
                }*/
            }
        });
    }
    
    @Override
    public void initializeAfterLoadingFxml() {
        getContext().getKeYMediator().addKeYSelectionListener(proofChangeListener);
    }
    
    public void addProofToBrowser() {
        String proofName = proof.name().toString();
        for (TreeItem<String> treeItem : PROOF_BROWSER_ROOT_NODE.getChildren()) {
            if (treeItem.getValue().equals(proofName)) {
                return;
            }
        }

        listOfProofs.put(proofName, proof);
        TreeItem<String> newProof = new TreeItem<String>(proofName);
        PROOF_BROWSER_ROOT_NODE.getChildren().add(newProof);
        tableView.getSelectionModel().select(newProof);
    }
    
    @FXML
    public void removeProofFromBrowser() {
        int i = tableView.getSelectionModel().getSelectedIndex() - 1;
        if (i < 0) {
            return;
        }
        listOfProofs.remove(tableView.getSelectionModel().getSelectedItem().getValue());
        PROOF_BROWSER_ROOT_NODE.getChildren().remove(i);
    }
}
