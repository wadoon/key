package de.uka.ilkd.key.java;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.services.GenericProofServices;

import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.proof.Counter;
import de.uka.ilkd.key.proof.NameRecorder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;

public interface ProofServices extends GenericProofServices {

    NameRecorder getNameRecorder();

    void saveNameRecorder(Node n);

    void addNameProposal(Name proposal);

    /** returns the theories of the logic */
    TheoryServices getTheories();

    SpecificationRepository getSpecificationRepository();

    /** 
     * Marks this services as proof specific 
     * Please make sure that the {@link Services} does not not yet belong to an existing proof 
     * or that it is owned by a proof environment. In both cases copy the {@link InitConfig} via
     * {@link InitConfig#deepCopy()} or one of the other copy methods first. 
     * @param p_proof the Proof to which this {@link Services} instance belongs
     */
    void setProof(Proof p_proof);

    /*
     * returns an existing named counter, creates a new one otherwise
     */
    Counter getCounter(String name);

    /**
     * sets the namespaces of known predicates, functions, variables
     * @param namespaces the NamespaceSet with the proof specific namespaces
     */
    void setNamespaces(NamespaceSet namespaces);

    /**
     * Returns the proof to which this object belongs, or null if it does not 
     * belong to any proof.
     */
    Proof getProof();

    /**
     * Returns the sued {@link Profile}.
     * @return The used {@link Profile}.
     */
    Profile getProfile();

}