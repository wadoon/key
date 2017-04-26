package de.uka.ilkd.key.api;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.KeYTypeUtil;
import org.key_project.util.collection.ImmutableSet;

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/**
 * This class serves as a facade to all functionalities that are needed for proof management, i.e.,
 * loading proof files, retrieving the proof obligations
 * Created by sarah.
 */
public class ProofManagementApi {
    private KeYEnvironment<?> currentEnv;
    private final List<Contract> proofContracts = new ArrayList<>();

    ProofManagementApi(KeYEnvironment env) {
        currentEnv = env;
    }

    Services getServices() {
        return currentEnv.getServices();
    }

    /**
     * Retrieve a list of all available contracts
     *
     * @return List<Contract>; can be null if no file was loaded before (we should throw an exception here)
     */
    public List<Contract> getProofContracts() {
        if (proofContracts.isEmpty())
            buildContracts();
        return proofContracts;
    }

    /**
     * constructs the possible proof contracts from the
     * java info in the environment.
     */
    private void buildContracts() {
        proofContracts.clear();
        Set<KeYJavaType> kjts = currentEnv.getJavaInfo().getAllKeYJavaTypes();
        for (KeYJavaType type : kjts) {
            if (!KeYTypeUtil.isLibraryClass(type)) {
                ImmutableSet<IObserverFunction> targets = currentEnv.getSpecificationRepository()
                        .getContractTargets(type);
                for (IObserverFunction target : targets) {
                    ImmutableSet<Contract> contracts = currentEnv.getSpecificationRepository()
                            .getContracts(type, target);
                    for (Contract contract : contracts) {
                        proofContracts.add(contract);
                    }
                }
            }
        }
    }

    /**
     * @param contract
     * @return
     * @throws ProofInputException
     */
    public ProofApi startProof(ProofOblInput contract) throws ProofInputException {
        return new ProofApi(currentEnv.createProof(contract), currentEnv);
    }

    /**
     * @param contract
     * @return
     * @throws ProofInputException
     */
    public ProofApi startProof(Contract contract) throws ProofInputException {
        return startProof(contract.createProofObl(currentEnv.getInitConfig(), contract));
    }

    public ProofApi getLoadedProof() {
        return new ProofApi(currentEnv.getLoadedProof(), currentEnv);
    }
}
