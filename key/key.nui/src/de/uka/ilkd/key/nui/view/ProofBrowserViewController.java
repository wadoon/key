package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.HashMap;
import java.util.ResourceBundle;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.proof.Proof;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.fxml.FXML;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

/**
 * Adds a {@link Proof} Browser {@link ViewController} to collect all loaded
 * {@link Proof}s in one place to be able to switch between them.
 * 
 * @author Nils Muzzulini
 * @version 1.0
 */
@KeYView(title = "Proofs", path = "ProofBrowserView.fxml", preferredPosition = ViewPosition.BOTTOMRIGHT)
public class ProofBrowserViewController extends ViewController {

    private final static TreeItem<String> PROOF_BROWSER_ROOT_NODE = new TreeItem<String>("Proofs");
    private HashMap<String, Proof> listOfProofs = new HashMap<String, Proof>();
    private Proof proof;

    @FXML
    private TreeView<String> proofBrowserTreeView;

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

    /**
     * {@inheritDoc}
     */
    @Override
    public void initialize(URL location, ResourceBundle resources) {
        PROOF_BROWSER_ROOT_NODE.setExpanded(true);
        proofBrowserTreeView.setRoot(PROOF_BROWSER_ROOT_NODE);
        proofBrowserTreeView.getSelectionModel().selectedItemProperty()
                .addListener(new ChangeListener<TreeItem<String>>() {
                    @Override
                    public void changed(ObservableValue<? extends TreeItem<String>> observable,
                            TreeItem<String> old_val, TreeItem<String> new_val) {
                        TreeItem<String> selectedItem = new_val;

                        Proof p = listOfProofs.get(selectedItem.getValue());
                        getContext().getKeYMediator().setProof(p);
                    }
                });
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void initializeAfterLoadingFxml() {
        getContext().getKeYMediator().addKeYSelectionListener(proofChangeListener);
    }

    /**
     * Adds a {@link Proof} to the Browser {@link TreeView}. Also adds an entry
     * to the {@link HashMap} of Proofs where the key is the {@link Name} of the
     * {@link Proof} and the corresponding value is the {@link Proof} itself.
     */
    private void addProofToBrowser() {
        String proofName = proof.name().toString();
        listOfProofs.put(proofName, proof);

        // TODO this does not allow duplicates. it is needed because
        // selectedProofChanged fires 4 times!!! Need to find out why and if
        // that can be changed
        for (TreeItem<String> treeItem : PROOF_BROWSER_ROOT_NODE.getChildren()) {
            if (treeItem.getValue().equals(proofName)) {
                return;
            }
        }
        
        TreeItem<String> newProof = new TreeItem<String>(proofName);
        PROOF_BROWSER_ROOT_NODE.getChildren().add(newProof);
        proofBrowserTreeView.getSelectionModel().select(newProof);
    }

    /**
     * Removes the selected {@link Proof} from the Browser {@link TreeView}.
     * Also removes the corresponding entry in the {@link HashMap} of Proofs.
     */
    @FXML
    private void discardSelectedProof() {
        int i = proofBrowserTreeView.getSelectionModel().getSelectedIndex() - 1;
        if (i < 0) {
            return;
        }
        listOfProofs.remove(proofBrowserTreeView.getSelectionModel().getSelectedItem().getValue());
        PROOF_BROWSER_ROOT_NODE.getChildren().remove(i);
    }
}
