package de.uka.ilkd.key.api;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.speclang.Contract;

import java.io.File;
import java.util.List;

/**
 * This class serves as a facade to all functionalities that are needed for proof management, i.e.,
 * loading proof files, retrieving the proof obligations
 * Created by sarah.
 */
public abstract class ProofManagement {

    private KeYEnvironment<?> currentEnv;

    /**
     * Load a proof file, creates a KeY environment that can be accessed with other methods from this facade
     * @param file Path to the source code folder/file or to a *.proof file
     * @param classPaths Optionally: Additional specifications for API classes
     * @param bootClassPath Optionally: Different default specifications for Java API
     * @param includes Optionally: Additional includes to consider
     *
     */
    public abstract void loadProofFile(File file, List<File> classPaths,
      File bootClassPath,  List<File> includes);

    /**
     * Retrieve a list of all available contracts
     * @return List<Contract>; can be null if no file was loaded before (we should throw an exception here)
     */
    public abstract List<Contract> getProofContracts();

    //getProofObligation(Contract)
    //loadProof (javadatei)
    /**
     * Save current Proof-> ProofApi
     */
    public abstract void saveProof();

    //public abstract void

}
