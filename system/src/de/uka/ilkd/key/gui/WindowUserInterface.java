package de.uka.ilkd.key.gui;



import java.io.File;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.DefaultJavaDLProblemLoader;
import de.uka.ilkd.key.proof.DefaultProblemLoader;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;

/**
 * This class is the starting point for the extraction of a unified
 * Userinterface for a GUI refactoring.
 * 
 * It gathers all present interfaces and redirects action to the mainWindow.
 * 
 * It is subject to change a lot at the moment.
 * 
 * @author mattias ulbrich
 */

public class WindowUserInterface extends AbstractWindowUserInterface<Services, InitConfig> {

    public WindowUserInterface(MainWindow<Services, InitConfig> mainWindow) {
        super(mainWindow);
        completions.add(new FunctionalOperationContractCompletion());
        completions.add(new DependencyContractCompletion());
        completions.add(new LoopInvariantRuleCompletion());
    }

    @Override
    public ProblemInitializer createProblemInitializer(boolean registerProof) {
        return new ProblemInitializer(this, mainWindow.getMediator().getProfile(), registerProof,  this);
    }

    @Override
    public DefaultProblemLoader<Services, InitConfig> createDefaultProblemLoader(
            File file, List<File> classPath, File bootClassPath,
            KeYMediator<Services, InitConfig> mediator) {
        return new DefaultJavaDLProblemLoader(file, classPath, bootClassPath, mediator);
    }
}
