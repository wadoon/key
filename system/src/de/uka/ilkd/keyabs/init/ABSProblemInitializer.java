package de.uka.ilkd.keyabs.init;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.proof.init.AbstractInitConfig;
import de.uka.ilkd.key.proof.init.AbstractProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.util.ProgressMonitor;

public class ABSProblemInitializer extends AbstractProblemInitializer {

    public ABSProblemInitializer(ProgressMonitor mon, Profile profile,
            IServices services, boolean registerProof,
            ProblemInitializerListener listener) {
        super(mon, profile, services, registerProof, listener);
    }

    @Override
    protected void registerProgramDefinedSymbols(AbstractInitConfig initConfig)
            throws ProofInputException {
    }

    @Override
    protected void readJava(EnvInput envInput, AbstractInitConfig initConfig)
            throws ProofInputException {
    }

}
