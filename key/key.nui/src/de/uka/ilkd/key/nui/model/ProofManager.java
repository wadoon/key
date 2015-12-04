package de.uka.ilkd.key.nui.model;

import java.io.File;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.MainApp;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

public class ProofManager {

    private Proof proof;
    private MainApp mainApp;
    
    /**
     * grant access to the mainapp
     * @param mainApp
     */
    public void setMainApp(MainApp mainApp) {
        this.mainApp = mainApp;
    }
    
    /**
     * Empty constructor.
     */
    public ProofManager() {
        
    }
    
    /**
     * This constructor sets the mainApp when instantiating.
     * @param mainApp The MainApp
     */
    public ProofManager(MainApp mainApp) {
        setMainApp(mainApp);
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
    public void setProof(File proofFile) {
        mainApp.setStatus("Loading Proof...");
        this.proof = loadProof(proofFile);
        mainApp.setStatus("Proof loaded: " + proofFile.getName());
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
            KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null,
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
