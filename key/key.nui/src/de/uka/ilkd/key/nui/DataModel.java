package de.uka.ilkd.key.nui;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.Observable;
import java.util.ResourceBundle;

import de.uka.ilkd.key.proof.Proof;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

/**
 * Class representing the data associated with the GUI.
 * 
 * @author Florian Breitfelder
 * @author Patrick Jattke
 *
 */
public class DataModel extends Observable {

    /**
     * HashMap storing the pairs of (String, {@link TreeViewState}), where
     * String represents the filename of the proof file.
     */
    private HashMap<String, TreeViewState> treeViewStates = new HashMap<String, TreeViewState>();

    /**
     * Represents the lastly stored TreeViewState, therefore it is displayed
     * currently in the TreeView
     */
    private TreeViewState loadedTreeViewState;

    /**
     * An instance representing the associated NUI.
     */
    private NUI nui;

    /**
     * References the currently loaded resource bundle in the {@link NUI}.
     */
    private ResourceBundle bundle;

    /**
     * Creates a new data model for the GUI instance.
     * 
     * @param nui
     *            The {@link NUI} instance associated to the data model.
     * @param bundle
     *            The current loaded resource bundle in the {@link NUI}.
     */
    public DataModel(NUI nui, ResourceBundle bundle) {
        this.nui = nui;
        this.bundle = bundle;
    }

    /**
     * Returns the {@link TreeViewState} associated to the given filename name.
     * 
     * @param name
     *            The key (filename of the proof) used to search for the
     *            TreeViewState.
     * @return TreeViewState The TreeViewState searched for.
     */
    public TreeViewState getTreeViewState(String name) {
        return treeViewStates.get(name);
    }

    /**
     * Stores a <b>new</b> TreeViewState into the list of TreeViewStates.
     * Overwrites the an existing state if the key is already present. <br>
     * Does check if the key already exists, if yes, then the modified flag is
     * set, see {@link TreeViewState#setModified(boolean)}.
     * 
     * @param treeViewState
     *            The new treeViewState to store.
     * @param name
     *            The name of the key associated with the state (filename of
     *            proof file).
     */
    public void saveTreeViewState(TreeViewState treeViewState, String name) {
        if (treeViewStates.containsKey(name)) {
            treeViewState.setModified(true);
        }
        treeViewStates.put(name, treeViewState);
        loadedTreeViewState = treeViewState;
        this.setChanged();
        this.notifyObservers(name);
    }

    /**
     * Returns the currently loaded TreeViewState.
     * 
     * @return TreeViewState currently loaded in the TreeView.
     */
    public TreeViewState getLoadedTreeViewState() {
        return loadedTreeViewState;
    }

    /**
     * Saves the proof file proof to the given File destinationFile.
     * 
     * @param proof
     *            the {@link Proof} file to be saved.
     * @param destinationFile
     *            the destination {@link File} where the proof is saved to.
     */
    public final void saveProof(Proof proof, File destinationFile) {
        try {
            proof.saveToFile(destinationFile);
            proof.setProofFile(destinationFile);
            nui.updateStatusbar(bundle.getString("savedSuccessfully") + " "
                    + destinationFile.getAbsolutePath());
            // If proof is successfully saved, unset isModified flag
            getLoadedTreeViewState().setModified(false);
        }
        catch (IOException e) {
            nui.updateStatusbar(e.getMessage());
        }
    }

    /**
     * Returns the list of filenames of currently loaded proofs.
     * 
     * @return An ObservableList&lt;String&gt; containing the filenames of the
     *         loaded proofs.
     */
    public ObservableList<String> getListOfProofs() {
        ObservableList<String> listOfProofs = FXCollections
                .observableArrayList();
        for (String proofName : treeViewStates.keySet()) {
            listOfProofs.add(proofName);
        }
        return listOfProofs;
    }

    /**
     * Loads a proof from the {@link DataModel#treeViewStates} list which
     * contains all proofs loaded during this session.
     * 
     * @param proofName
     *            The filename of the proof to be loaded.
     */
    public void loadProofFormMemory(String proofName) {
        loadedTreeViewState = treeViewStates.get(proofName);
        this.setChanged();
        this.notifyObservers(proofName);
    }

    /**
     * Removes a TreeViewState from the list of loaded
     * {@link DataModel#treeViewStates treeViewStates}.
     * 
     * @param proofName
     *            The proof's filename associated with the TreeViewState.
     */
    public void removeProof(String proofName) {
        if (loadedTreeViewState.equals(treeViewStates.get(proofName))) {
            loadedTreeViewState = null;
        }
        treeViewStates.remove(proofName);
        this.setChanged();
        this.notifyObservers(proofName);
    }

}
