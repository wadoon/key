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
import de.uka.ilkd.key.proof.mgt.ProofStatus;
import javafx.application.Platform;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;

/**
 * Adds a {@link Proof} Browser {@link ViewController} to collect all loaded
 * {@link Proof}s in one place to be able to switch between them.
 * 
 * @author Nils Muzzulini
 * @version 1.0
 */
@KeYView(title = "Proofs", path = "ProofBrowserView.fxml", preferredPosition = ViewPosition.BOTTOMRIGHT)
public class ProofBrowserViewController extends ViewController {

    private final static Image CLOSED_PROOF_IMAGE = new Image("file:resources/images/keyproved.gif");
    private final static Image OPEN_PROOF_IMAGE = new Image("file:resources/images/ekey-mono.gif");
    private final static Image CLOSED_PROOF_BUT_OPEN_LEMMAS_LEFT_IMAGE = new Image("file:resources/images/ekey-brackets.gif");
    private final static TreeItem<String> PROOF_BROWSER_ROOT_NODE = new TreeItem<String>("Proofs");
    private HashMap<String, Proof> listOfProofs = new HashMap<String, Proof>();
    private Proof proof = null;
    private Node proofIcon;
    
    @FXML
    private Button discardProofButton;

    @FXML
    private TreeView<String> proofBrowserTreeView;

    // Listens for Proof or Node changes.
    private KeYSelectionListener proofChangeListener = new KeYSelectionListener() {
        @Override
        public void selectedProofChanged(KeYSelectionEvent event) {
            proof = event.getSource().getSelectedProof();
            addProofToBrowser(proof);
        }

        @Override
        public void selectedNodeChanged(KeYSelectionEvent event) {
            Platform.runLater(() -> {
                proof = event.getSource().getSelectedProof();
                updateImage(proof);
                proofBrowserTreeView.getSelectionModel().getSelectedItem().setGraphic(proofIcon);
            });
        }
    };

    // Selection Listener that sets the selected Proof in the Mediator.
    private ChangeListener<TreeItem<String>> browserSelectionListener = new ChangeListener<TreeItem<String>>() {
        @Override
        public void changed(ObservableValue<? extends TreeItem<String>> observable, TreeItem<String> old_val,
                TreeItem<String> new_val) {
            TreeItem<String> selectedItem = new_val;

            if (selectedItem.equals(PROOF_BROWSER_ROOT_NODE) || !selectedItem.isLeaf()) {
                discardProofButton.setDisable(true);
                return;
            }
            //discardProofButton.setDisable(false);
            Proof p = listOfProofs.get(selectedItem.getValue());
            getContext().getKeYMediator().setProof(p);
        }
    };

    /**
     * {@inheritDoc}
     */
    @Override
    public void initialize(URL location, ResourceBundle resources) {
        proofBrowserTreeView.setRoot(PROOF_BROWSER_ROOT_NODE);

        // Attach the selection listener to the Proof Browser tree view.
        Platform.runLater(() -> {
            proofBrowserTreeView.getSelectionModel().selectedItemProperty().addListener(browserSelectionListener);
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
     * Updates the image for a given proof.
     */
    private void updateImage(Proof proof) {
        ProofStatus ps = proof.mgt().getStatus();
        if (ps.getProofClosed()) {
            proofIcon = new ImageView(CLOSED_PROOF_IMAGE);
        } else if (ps.getProofClosedButLemmasLeft()) {
            proofIcon = new ImageView(CLOSED_PROOF_BUT_OPEN_LEMMAS_LEFT_IMAGE);
        } else {
            assert ps.getProofOpen();
            proofIcon = new ImageView(OPEN_PROOF_IMAGE);
        }
    }

    /**
     * Adds a {@link Proof} to the Browser {@link TreeView}. Also adds an entry
     * to the {@link HashMap} of Proofs where the key is the {@link Name} of the
     * {@link Proof} and the corresponding value is the {@link Proof} itself.
     * 
     * @param proof
     *            The {@link Proof} to be added to the Proof Browser.
     */
    private void addProofToBrowser(Proof proof) {
        String proofName = proof.name().toString();
        listOfProofs.put(proofName, proof);

        updateImage(proof);

        TreeItem<String> newProof = new TreeItem<String>(proofName, proofIcon);
        boolean found = false;

        for (TreeItem<String> environmentNode : PROOF_BROWSER_ROOT_NODE.getChildren()) {

            // TODO the following for-loop does not allow duplicates. It checks
            // whether an Environment node already contains the proof to be
            // added. If that is the case the method returns. It is needed
            // because selectedProofChanged fires 4 times!!! Need to find out
            // why and if that can be changed. The most recently opened proof is
            // added to the browser.
            for (TreeItem<String> treeItem : environmentNode.getChildren()) {
                if (treeItem.getValue().equals(proofName)) {
                    proofBrowserTreeView.getSelectionModel().select(treeItem);
                    Platform.runLater(() -> {
                        treeItem.setGraphic(proofIcon);
                    });
                    return;
                }
            }

            if (environmentNode.getValue().contentEquals(proof.getEnv().toString())) {
                environmentNode.getChildren().add(newProof);
                found = true;
                break;
            }
        }

        if (!found) {
            TreeItem<String> newEnvironmentNode = new TreeItem<String>(proof.getEnv().toString());
            PROOF_BROWSER_ROOT_NODE.getChildren().add(newEnvironmentNode);
            newEnvironmentNode.getChildren().add(newProof);
        }

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
