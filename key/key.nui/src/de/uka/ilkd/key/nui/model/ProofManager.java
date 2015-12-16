package de.uka.ilkd.key.nui.model;

import java.io.File;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.Context;
import de.uka.ilkd.key.nui.MainApp;
import de.uka.ilkd.key.nui.util.IStatusManager;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

public class ProofManager {

    private Proof proof;
    private IStatusManager status;
    private List<IProofListener> listeners = new ArrayList<IProofListener>();

    /**
     * Creates a new Proofmanager
     * @param status a StatusManager to print status texts to
     */
    public ProofManager(IStatusManager status) {
        this.status = status;
    }

    public synchronized void addProofListener(IProofListener proofListener) {
        this.listeners.add(proofListener);
    }

    public synchronized void removeProofListener(IProofListener proofListener) {
        this.listeners.remove(proofListener);
    }

    private synchronized void fireProofUpdatedEvent() {
        ProofEvent proofEvent = new ProofEvent(this.proof);
        Iterator<IProofListener> listeners = this.listeners.iterator();
        while (listeners.hasNext()) {
            ((IProofListener) listeners.next()).proofUpdated(proofEvent);
        }
    }
    
    /**
     * Getter method for a proof.
     * 
     * @return The loaded Proof.
     */
    public Proof getProof() {
        return this.proof;
    }

    /**
     * Load a Proof.
     * 
     * @param file
     *            Proof to be loaded.
     */
    public synchronized void setProof(File proofFile) {
        // this.proof.setProofFile(proofFile);
        status.setStatus("Loading Proof...");
        this.proof = loadProof(proofFile);
        status.setStatus("Proof loaded: " + proofFile.getName());
        fireProofUpdatedEvent();
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     * @return The loaded proof.
     */
    private Proof loadProof(File proofFile) {
        // File proofFile = new File("../" + proofFileName);

        try {
            KeYEnvironment<?> environment = KeYEnvironment.load(
                    JavaProfile.getDefaultInstance(), proofFile, null, null,
                    null, true);
            Proof proof = environment.getLoadedProof();

            return proof;
        }
        catch (ProblemLoaderException e) {
            e.printStackTrace();
            return null;
        }
    }
}
