package de.uka.ilkd.key.ui;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;

public class ConsoleUserInterface extends AbstractConsoleUserInterface<Services, InitConfig> {

    public ConsoleUserInterface(BatchMode batchMode, boolean verbose) {
        super(batchMode, verbose);
    }

    @Override
    public ProblemInitializer createProblemInitializer(boolean registerProof) {
       return new ProblemInitializer(this, getMediator().getProfile(), registerProof, this);
    }
    
}
