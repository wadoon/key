package de.uka.ilkd.key.ui;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.DefaultJavaDLProblemLoader;
import de.uka.ilkd.key.proof.DefaultProblemLoader;
import de.uka.ilkd.key.proof.init.JavaDLInitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;

public class ConsoleUserInterface extends AbstractConsoleUserInterface<Services, JavaDLInitConfig> {

    public ConsoleUserInterface(BatchMode batchMode, boolean verbose) {
        super(batchMode, verbose);
    }

    @Override
    public ProblemInitializer createProblemInitializer(boolean registerProof) {
       return new ProblemInitializer(this, getMediator().getProfile(), registerProof, this);
    }

    @Override
    public DefaultProblemLoader<Services, JavaDLInitConfig> createDefaultProblemLoader(
            File file, List<File> classPath, File bootClassPath,
            KeYMediator<Services, JavaDLInitConfig> mediator) {
        return new DefaultJavaDLProblemLoader(file, classPath, bootClassPath, mediator);
    }
    
}
