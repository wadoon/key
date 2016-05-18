package de.uka.ilkd.key.proof.io;

import java.io.IOException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;

/**
 * Loads a problem from a string.
 * 
 * @author Kai Wallisch
 *
 */
public class StringProblemLoader extends AbstractProblemLoader {

    private final String problem;

    public StringProblemLoader(String problem, ProblemLoaderControl control) {
        super(control);
        this.problem = problem;
    }

    @Override
    protected EnvInput createEnvInput() {
        return new EnvInputFromString(problem);
    }

    @Override
    protected LoadedPOContainer createProofObligationContainerFromJavaClass(String proofObligation) throws IOException {
        throw new UnsupportedOperationException(
                "Java file access is not supported in " + StringProblemLoader.class.getName());
    }

    @Override
    protected ProblemInitializer createProblemInitializer() {
        return new ProblemInitializer(control, new Services(envInput.getProfile()), control);
    }

    @Override
    protected ProofAggregate createProofAggregate(LoadedPOContainer poContainer)
            throws ProofInputException, ProblemLoaderException {
        ProofAggregate proofList = problemInitializer.startProver(initConfig, poContainer.getProofOblInput());
        for (Proof p : proofList.getProofs()) {
            // register proof
            initConfig.getServices().getSpecificationRepository().registerProof(poContainer.getProofOblInput(), p);
        }
        return proofList;
    }

}
